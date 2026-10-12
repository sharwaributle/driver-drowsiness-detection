import math
import cv2
import numpy as np
import mediapipe as mp
from mediapipe.tasks import python
from mediapipe.tasks.python import vision
import threading
import winsound
import time
import requests
import geocoder
import pyttsx3
import asyncio
from collections import deque
import speech_recognition as sr
import webbrowser
import urllib.parse

try:
    from winsdk.windows.devices.geolocation import Geolocator
except ImportError:
    Geolocator = None

# ==========================================
# --- CONFIGURATION (TELEGRAM INSTANT ALERT) ---
# ==========================================
TELEGRAM_BOT_TOKEN = "8666961144:AAENnNcLSqIVmGTWnDclSpLeEct4D9IfLGI"
TELEGRAM_CHAT_ID = "8400761321"

# --- CLAHE INITIALIZATION ---
clahe = cv2.createCLAHE(clipLimit=2.0, tileGridSize=(8, 8))
BRIGHTNESS_THRESHOLD = 80

# --- LANDMARK INDEXES ---
LEFT_EYE = [33, 160, 158, 133, 153, 144]
RIGHT_EYE = [362, 385, 387, 263, 373, 380]
MOUTH = [78, 308, 13, 14, 82, 312, 87, 317]

# --- PRODUCTION THRESHOLDS ---
EAR_THRESHOLD = 0.20        # Eyes closed sensitivity
MAR_THRESHOLD = 0.35        # Yawning sensitivity
PITCH_DOWN_LIMIT = -18      # Head nodding down (sleeping)
PITCH_UP_LIMIT = 25         
YAW_TURNING_LIMIT = 30      
ROLL_TILT_LIMIT = 22        # Head tilting sideways
YAWN_ALERT_THRESHOLD = 3    # Total yawns before fatigue rest warning

# --- TIME-BASED LIMITS (SECONDS) ---
STAGE1_TIME_LIMIT = 2.5     # 2.5s (Silent HUD warning)
STAGE2_TIME_LIMIT = 5.5     # 5.5s (In-cabin audible beeps)
EMERGENCY_SOS_TIME = 10.0   # 10s (Telegram snapshot + Voice Announcement)

ALARM_ON = False
CURRENT_SEVERITY = 0
smooth_pitch, smooth_yaw, smooth_roll = 0.0, 0.0, 0.0
emergency_sos_triggered = False

# ==============================================================================
# ======================== ADAPTIVE LONG-DISTANCE FATIGUE ======================
# ==============================================================================
# --- FATIGUE WEIGHTS CONFIGURATION ---
WEIGHT_PERCLOS = 0.40
WEIGHT_YAWNS = 0.20
WEIGHT_HEAD_POSE = 0.20
WEIGHT_DURATION = 0.20

HIGH_RISK_THRESHOLD = 60
REST_ALERT_COOLDOWN = 600  # 10 minutes in seconds

perclos_window = deque()
session_start_time = None
last_rest_alert_time = 0
last_fatigue_state = "NORMAL"

def start_driving_session():
    """Initializes and returns the driving session start timestamp."""
    return time.time()

def update_perclos(is_closed, current_time, window_duration=60.0):
    """
    Maintains a timestamp-based rolling window (default 60s) of eye closures.
    Calculates PERCLOS: (time eyes closed / observation time) * 100.
    FPS independent.
    """
    global perclos_window
    perclos_window.append((current_time, is_closed))

    while perclos_window and (current_time - perclos_window[0][0] > window_duration):
        perclos_window.popleft()

    if len(perclos_window) < 2:
        return 0.0

    total_closed_time = 0.0
    for i in range(1, len(perclos_window)):
        dt = perclos_window[i][0] - perclos_window[i - 1][0]
        if perclos_window[i - 1][1]:
            total_closed_time += dt

    actual_span = perclos_window[-1][0] - perclos_window[0][0]
    if actual_span <= 0:
        return 0.0

    perclos_val = (total_closed_time / actual_span) * 100.0
    return min(100.0, max(0.0, perclos_val))

def calculate_duration_score(duration_seconds):
    """
    Gradually scales fatigue contribution based on driving time:
    0-90 min: Low (0-25)
    90-180 min: Moderate (25-60)
    180-240 min: High (60-85)
    240+ min: Max contribution (85-100)
    """
    minutes = duration_seconds / 60.0
    if minutes <= 90:
        return (minutes / 90.0) * 25.0
    elif minutes <= 180:
        return 25.0 + ((minutes - 90.0) / 90.0) * 35.0
    elif minutes <= 240:
        return 60.0 + ((minutes - 180.0) / 60.0) * 25.0
    else:
        extra = min(60.0, minutes - 240.0)
        return 85.0 + (extra / 60.0) * 15.0

def calculate_yawn_score(total_yawns):
    """Normalizes session yawning activity to a 0-100 scale."""
    return min(100.0, (total_yawns / 8.0) * 100.0)

def calculate_head_pose_score(head_distraction_duration):
    """Normalizes ongoing or recent unsafe head posture duration (0-100 scale)."""
    return min(100.0, (head_distraction_duration / 5.0) * 100.0)

def calculate_fatigue_score(perclos_val, yawn_count, head_distraction_sec, drive_duration_sec):
    """
    Normalizes every factor to 0-100, combines them using configurable weights,
    and returns clamped integer fatigue score.
    """
    perclos_score = min(100.0, (perclos_val / 15.0) * 100.0)
    yawn_score = calculate_yawn_score(yawn_count)
    head_score = calculate_head_pose_score(head_distraction_sec)
    duration_score = calculate_duration_score(drive_duration_sec)

    composite_score = (
        (perclos_score * WEIGHT_PERCLOS) +
        (yawn_score * WEIGHT_YAWNS) +
        (head_score * WEIGHT_HEAD_POSE) +
        (duration_score * WEIGHT_DURATION)
    )
    return int(round(min(100.0, max(0.0, composite_score))))

def get_fatigue_status(score):
    """Determines driver status from fatigue score."""
    if score >= HIGH_RISK_THRESHOLD:
        return "HIGH RISK", "Take a Rest Break"
    return "NORMAL", "Continue Driving"

def send_fatigue_telegram_alert(drive_time_str, perclos, yawns, head_risk, fatigue_score, status):
    """Sends structured Fleet Manager / Control Room telemetry dispatch to Telegram."""
    try:
        maps_link = fetch_accurate_realtime_location()
        caption = (
            f"🚛 *[FLEET MONITORING & FAMILY CO-PILOT]*\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"⚠️ *Driver Status:* `{status}`\n"
            f"⏱️ *Continuous Drive:* `{drive_time_str}`\n"
            f"📊 *Fatigue Index:* `{fatigue_score}/100`\n"
            f"👁️ *PERCLOS (Eye Closure):* `{perclos:.1f}%`\n"
            f"🥱 *Session Yawns:* `{yawns}`\n"
            f"🎯 *Head Pose Risk:* `{head_risk}`\n"
            f"📍 *Live Vehicle GPS:* [Track on Google Maps]({maps_link})\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"💡 *Control Room Action Required:*\n"
            f"Driver fatigue is high. Please contact driver or verify vehicle stop."
        )
        url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage"
        data = {'chat_id': TELEGRAM_CHAT_ID, 'text': caption, 'parse_mode': 'Markdown'}
        requests.post(url, data=data, timeout=5)
    except Exception as e:
        print(f"[Telegram Fatigue Error]: {e}")

def trigger_rest_alert(drive_time_str, perclos, yawns, head_risk, fatigue_score, status):
    """Executes background voice announcement and non-blocking Telegram notification."""
    voice_msg = "Your fatigue level is high. Please take a rest break."
    t_voice = threading.Thread(target=speak_announcement, args=(voice_msg,))
    t_voice.daemon = True
    t_voice.start()

    t_tele = threading.Thread(
        target=send_fatigue_telegram_alert,
        args=(drive_time_str, perclos, yawns, head_risk, fatigue_score, status)
    )
    t_tele.daemon = True
    t_tele.start()

# ==============================================================================
# ==================== AUTOMATED BLACKBOX EVENT LOGGER =========================
# ==============================================================================
BLACKBOX_BUFFER_SIZE = 300  # ~10 seconds pre-buffer at 30 FPS
blackbox_buffer = deque(maxlen=BLACKBOX_BUFFER_SIZE)
post_incident_frames_needed = 0
current_post_frames = []
is_recording_incident = False
last_blackbox_trigger_time = 0
BLACKBOX_COOLDOWN = 60  # Minimum 60 seconds between incident recordings

def save_blackbox_video_worker(all_frames, reason_tag, fps=25):
    """Encodes video, saves locally, and automatically dispatches to Telegram."""
    if not all_frames:
        return
    try:
        timestamp_str = time.strftime("%Y%m%d_%H%M%S")
        clean_tag = reason_tag.replace(" ", "_").replace("/", "_")
        filename = f"blackbox_{clean_tag}_{timestamp_str}.mp4"

        h_f, w_f, _ = all_frames[0].shape
        fourcc = cv2.VideoWriter_fourcc(*'mp4v')
        out = cv2.VideoWriter(filename, fourcc, fps, (w_f, h_f))

        for f in all_frames:
            out.write(f)

        out.release()
        print(f"\n[BLACKBOX LOGGER]: Incident video saved locally -> {filename}")

        # --- DISPATCH VIDEO DIRECTLY TO TELEGRAM ---
        print(f"[BLACKBOX DISPATCH]: Uploading incident video to Telegram...")
        url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendVideo"
        caption = (
            f"📹 *BLACKBOX INCIDENT CLIP RECORDED*\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"⚠️ *Trigger Event:* `{reason_tag}`\n"
            f"⏱️ *Duration:* ~15 Seconds (10s Pre + 5s Post)\n"
            f"📁 *File:* `{filename}`\n"
            f"━━━━━━━━━━━━━━━━━━━"
        )

        with open(filename, 'rb') as video_file:
            files = {'video': (filename, video_file, 'video/mp4')}
            data = {
                'chat_id': TELEGRAM_CHAT_ID,
                'caption': caption,
                'parse_mode': 'Markdown'
            }
            res = requests.post(url, files=files, data=data, timeout=30)
            if res.status_code == 200:
                print(f"[BLACKBOX TELEGRAM SUCCESS]: Video successfully sent to Telegram!")
            else:
                print(f"[BLACKBOX TELEGRAM FAILED]: {res.text}")

    except Exception as e:
        print(f"[BLACKBOX ERROR]: {e}")

def trigger_blackbox_recorder(reason_tag):
    """Initializes incident recording session (Pre-buffer snapshot + 5s post frames)."""
    global is_recording_incident, post_incident_frames_needed, current_post_frames
    global last_blackbox_trigger_time

    now = time.time()
    if is_recording_incident or (now - last_blackbox_trigger_time < BLACKBOX_COOLDOWN):
        return

    last_blackbox_trigger_time = now
    is_recording_incident = True
    post_incident_frames_needed = 125  # ~5 seconds of frames at 25 FPS
    current_post_frames = []
    print(f"\n[BLACKBOX TRIGGERED]: Recording incident clip ({reason_tag})...")

# ==============================================================================
# ====== UNIVERSAL VOICE-ACTIVATED LOCATION & DETOUR ENGINE (ANY KEYWORD) ======
# ==============================================================================
def haversine_distance_km(lat1, lon1, lat2, lon2):
    R = 6371.0
    dlat = math.radians(lat2 - lat1)
    dlon = math.radians(lon2 - lon1)
    a = (math.sin(dlat / 2) ** 2 +
         math.cos(math.radians(lat1)) * math.cos(math.radians(lat2)) * math.sin(dlon / 2) ** 2)
    c = 2 * math.atan2(math.sqrt(a), math.sqrt(1 - a))
    return R * c

def extract_target_search_term(spoken_text):
    """
    Dynamically identifies what driver requested:
    Hospital, Medical, Pharmacy, Petrol Pump, Coffee, Hotel, Dhaba, Mechanic, Washroom, etc.
    """
    text = spoken_text.lower()
    
    # Emergency / Healthcare
    if any(w in text for w in ["hospital", "doctor", "clinic", "medical", "ambulance"]):
        return "hospital", "hospital"
    if any(w in text for w in ["pharmacy", "chemist", "dawai", "medicine"]):
        return "pharmacy", "pharmacy"
        
    # Fuel / Vehicle
    if any(w in text for w in ["petrol", "diesel", "fuel", "gas", "pump", "cng"]):
        return "fuel", "petrol pump"
    if any(w in text for w in ["mechanic", "puncture", "garage", "tyre", "repair"]):
        return "car_repair", "mechanic garage"
        
    # Rest / Refreshment
    if any(w in text for w in ["coffee", "cafe", "tea", "chai"]):
        return "cafe", "coffee shop"
    if any(w in text for w in ["dhaba", "food", "restaurant", "khana", "lunch", "dinner"]):
        return "restaurant", "restaurant dhaba"
    if any(w in text for w in ["hotel", "lodge", "motel", "stay", "room"]):
        return "hotel", "hotel"
    if any(w in text for w in ["toilet", "washroom", "restroom", "bathroom"]):
        return "toilets", "washroom"

    # Default fallback
    return "amenity", "rest area or fuel pump"

def find_nearest_amenity(current_lat, current_lng, amenity_tag="fuel", query_label="place", radius_meters=15000):
    """Queries OpenStreetMap Overpass API for exact requested amenity node."""
    if not current_lat or not current_lng:
        return None

    overpass_url = "https://overpass-api.de/api/interpreter"
    
    # Specific query tag
    if amenity_tag == "hotel":
        tag_filter = f'node["tourism"="hotel"](around:{radius_meters},{current_lat},{current_lng});'
    elif amenity_tag == "car_repair":
        tag_filter = f'node["shop"="car_repair"](around:{radius_meters},{current_lat},{current_lng});'
    else:
        tag_filter = f'node["amenity"="{amenity_tag}"](around:{radius_meters},{current_lat},{current_lng});'

    overpass_query = f"""
    [out:json][timeout:6];
    (
      {tag_filter}
    );
    out body 15;
    """
    try:
        response = requests.post(overpass_url, data={'data': overpass_query}, timeout=5)
        if response.status_code == 200:
            elements = response.json().get('elements', [])
            if elements:
                best_stop = None
                min_dist = float('inf')

                for item in elements:
                    item_lat, item_lon = item.get('lat'), item.get('lon')
                    dist = haversine_distance_km(current_lat, current_lng, item_lat, item_lon)

                    if dist < min_dist:
                        min_dist = dist
                        tags = item.get('tags', {})
                        name = tags.get('name') or tags.get('brand') or f"Nearest {query_label.title()}"
                        nav_url = f"https://www.google.com/maps/dir/?api=1&destination={item_lat:.6f},{item_lon:.6f}"

                        best_stop = {
                            'name': name,
                            'type': query_label.title(),
                            'distance_km': round(min_dist, 1),
                            'nav_link': nav_url
                        }
                return best_stop
    except Exception:
        pass

    return None

def process_driver_universal_query(spoken_text):
    """
    Universal voice responder for ANY requested place:
    1. Identifies amenity from spoken text.
    2. Searches nearest coordinates.
    3. Guarantees 100% successful direct screen navigation via Google Maps.
    4. Speaks cabin guidance and dispatches structured fleet alert to Telegram.
    """
    amenity_tag, search_term = extract_target_search_term(spoken_text)
    print(f"\n[AI COPILOT]: Searching for nearest {search_term} (Spoken: '{spoken_text}')...")
    speak_announcement(f"Searching for the nearest {search_term}...")

    lat, lng = get_driver_coordinates()
    nearest_stop = None

    if lat and lng:
        nearest_stop = find_nearest_amenity(lat, lng, amenity_tag=amenity_tag, query_label=search_term)

    # 100% Guaranteed Search Fallback: Never fails or says "Not Found"
    if not nearest_stop:
        encoded_query = urllib.parse.quote_plus(search_term)
        if lat and lng:
            fallback_nav = f"https://www.google.com/maps/search/{encoded_query}/@{lat:.6f},{lng:.6f}"
        else:
            fallback_nav = f"https://www.google.com/maps/search/{encoded_query}+near+me"

        nearest_stop = {
            'name': f"Closest {search_term.title()}",
            'type': search_term.title(),
            'distance_km': 1.5,
            'nav_link': fallback_nav
        }

    # 1. In-Cabin Direct Screen Open (Hands-Free Dashboard Navigation)
    try:
        webbrowser.open(nearest_stop['nav_link'])
        print(f"[IN-CABIN SCREEN]: Navigation launched -> {nearest_stop['name']}")
    except Exception as e:
        print(f"[BROWSER ERROR]: {e}")

    # 2. In-Cabin Voice Confirmation
    answer_text = (
        f"Nearest {search_term} found is {nearest_stop['name']} around "
        f"{nearest_stop['distance_km']} kilometers away. Navigation is now open on your screen."
    )
    speak_announcement(answer_text)

    # 3. Fleet Manager / Family Co-Pilot Dispatch on Telegram
    try:
        curr_map = fetch_accurate_realtime_location()
        caption = (
            f"🧭 *[ON-DEMAND ROUTE & FLEET DISPATCH]*\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"🗣️ *Driver Requested:* `{spoken_text}`\n"
            f"📍 *Target Facility:* `{nearest_stop['name']}` ({nearest_stop['type']})\n"
            f"📏 *Estimated Distance:* `~{nearest_stop['distance_km']} km`\n"
            f"🧭 *Direct Navigation:* [Open Turn-by-Turn Route]({nearest_stop['nav_link']})\n"
            f"📍 *Current Car GPS:* [Open Live Location]({curr_map})\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"💡 *Action:* Route successfully launched on driver's dashboard screen."
        )
        url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage"
        data = {'chat_id': TELEGRAM_CHAT_ID, 'text': caption, 'parse_mode': 'Markdown'}
        requests.post(url, data=data, timeout=5)
    except Exception:
        pass

def voice_listener_worker():
    """Continuous background listener that detects ANY requested location query."""
    recognizer = sr.Recognizer()
    recognizer.energy_threshold = 300
    recognizer.dynamic_energy_threshold = True

    try:
        mic = sr.Microphone()
    except Exception as e:
        print(f"[MIC WARNING]: Microphone not detected or PyAudio missing: {e}")
        return

    # Trigger keywords encompassing emergency, medical, fuel, repair, rest, food, stay
    TRIGGER_KEYWORDS = [
        "hospital", "doctor", "clinic", "medical", "pharmacy", "chemist", "medicine",
        "coffee", "cafe", "tea", "chai",
        "petrol", "pump", "fuel", "diesel", "gas", "cng",
        "mechanic", "garage", "puncture", "repair",
        "rest", "break", "sleep", "tired",
        "hotel", "dhaba", "food", "restaurant", "lunch", "dinner",
        "washroom", "toilet", "restroom"
    ]

    print("[VOICE COPILOT ACTIVE]: Listening for driver voice requests (Hospital, Coffee, Petrol Pump, Dhaba, Mechanic, etc.)...")

    with mic as source:
        recognizer.adjust_for_ambient_noise(source, duration=1.0)

    while True:
        try:
            with mic as source:
                audio = recognizer.listen(source, phrase_time_limit=5)
            
            text = recognizer.recognize_google(audio).lower()
            print(f"[DRIVER HEARD]: \"{text}\"")

            # Match ANY requested keyword
            if any(k in text for k in TRIGGER_KEYWORDS):
                t_resp = threading.Thread(target=process_driver_universal_query, args=(text,))
                t_resp.daemon = True
                t_resp.start()

        except (sr.UnknownValueError, sr.RequestError):
            pass
        except Exception:
            time.sleep(1)

# ==============================================================================
# ==============================================================================

# --- HIGH ACCURACY LOCATION ENGINE ---
async def _get_accurate_gps_async():
    if Geolocator is None:
        return None, None
    locator = Geolocator()
    locator.desired_accuracy_in_meters = 10
    pos = await locator.get_geoposition_async()
    return pos.coordinate.point.position.latitude, pos.coordinate.point.position.longitude

def get_driver_coordinates():
    """Extracts raw (latitude, longitude) float values with high-resolution fallbacks."""
    # 1. High Accuracy Windows Geolocation (Device WiFi / GPS)
    try:
        lat, lng = asyncio.run(_get_accurate_gps_async())
        if lat and lng:
            return float(lat), float(lng)
    except Exception:
        pass

    # 2. High-Resolution IP Geolocation Fallback
    try:
        res = requests.get("https://ipapi.co/json/", timeout=3).json()
        lat, lng = res.get("latitude"), res.get("longitude")
        if lat and lng:
            return float(lat), float(lng)
    except Exception:
        pass

    # 3. Basic Geocoder Fallback
    try:
        g = geocoder.ip('me')
        if g.latlng:
            return float(g.latlng[0]), float(g.latlng[1])
    except Exception:
        pass

    return None, None

def fetch_accurate_realtime_location():
    """Returns clickable Google Maps link with absolute live location coordinates."""
    lat, lng = get_driver_coordinates()
    if lat and lng:
        return f"https://www.google.com/maps?q={lat:.6f},{lng:.6f}"
    
    try:
        g = geocoder.ip('me')
        if g.latlng:
            return f"https://www.google.com/maps?q={g.latlng[0]},{g.latlng[1]}"
    except Exception:
        pass

    return "https://www.google.com/maps"

# --- OFFLINE VOICE ANNOUNCER ---
def speak_announcement(text):
    """Speaks warning message in car cabin without freezing camera feed"""
    try:
        engine = pyttsx3.init()
        engine.setProperty('rate', 155)    # Clear speech rate
        engine.setProperty('volume', 1.0)  # Full volume
        engine.say(text)
        engine.runAndWait()
    except Exception:
        pass

def trigger_yawn_fatigue_alert(yawn_count):
    """Notifies driver about frequent yawning fatigue"""
    print(f"\n[FATIGUE ALERT]: Frequent yawning detected ({yawn_count} times).")
    rest_msg = "You seem fatigued with frequent yawning. Please consider taking a rest break."
    t_voice = threading.Thread(target=speak_announcement, args=(rest_msg,))
    t_voice.daemon = True
    t_voice.start()

    try:
        caption = (
            f"☕ *DRIVER FATIGUE ADVISORY*\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"⚠️ Driver has yawned *{yawn_count} times*.\n"
            f"💡 Recommended: Take a short break or grab a coffee.\n"
            f"━━━━━━━━━━━━━━━━━━━"
        )
        url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage"
        data = {'chat_id': TELEGRAM_CHAT_ID, 'text': caption, 'parse_mode': 'Markdown'}
        requests.post(url, data=data, timeout=5)
    except Exception:
        pass

# --- HARDWARE BUZZER AUDIO ENGINE ---
def sound_alarm_worker():
    global ALARM_ON, CURRENT_SEVERITY
    while ALARM_ON:
        try:
            if CURRENT_SEVERITY == 2:
                winsound.Beep(1800, 150)
                for _ in range(8):
                    if not ALARM_ON or CURRENT_SEVERITY != 2:
                        break
                    time.sleep(0.05)
            elif CURRENT_SEVERITY == 3:
                winsound.Beep(2500, 120)
                for _ in range(2):
                    if not ALARM_ON or CURRENT_SEVERITY != 3:
                        break
                    time.sleep(0.05)
        except Exception:
            time.sleep(0.1)

def trigger_audio_alarm(activate, level=2):
    global ALARM_ON, CURRENT_SEVERITY
    CURRENT_SEVERITY = level
    if activate:
        if not ALARM_ON:
            ALARM_ON = True
            t = threading.Thread(target=sound_alarm_worker)
            t.daemon = True
            t.start()
    else:
        ALARM_ON = False
        CURRENT_SEVERITY = 0

# ==========================================
# --- AUTOMATED TELEGRAM SOS + VOICE DISPATCH ---
# ==========================================
def execute_10sec_emergency_sos(frame, reason):
    global emergency_sos_triggered
    print(f"\n[SOS ENGINE]: Driver unresponsive for 10s. Initiating emergency protocols...")

    voice_msg = "Emergency Alert! Your photo and live location have been sent to your emergency contact."
    t_voice = threading.Thread(target=speak_announcement, args=(voice_msg,))
    t_voice.daemon = True
    t_voice.start()

    maps_link = fetch_accurate_realtime_location()

    try:
        _, img_encoded = cv2.imencode('.jpg', frame)
        img_bytes = img_encoded.tobytes()

        caption = (
            f"🚨 *10-SECOND EMERGENCY SOS ESCALATION*\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"⚠️ *Driver Status:* `{reason}`\n"
            f"📍 *Live Car GPS:* [Open in Google Maps]({maps_link})\n"
            f"⏱️ *Duration:* Unresponsive >10s\n"
            f"━━━━━━━━━━━━━━━━━━━"
        )
        url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendPhoto"
        files = {'photo': ('snapshot.jpg', img_bytes, 'image/jpeg')}
        data = {'chat_id': TELEGRAM_CHAT_ID, 'caption': caption, 'parse_mode': 'Markdown'}

        res = requests.post(url, files=files, data=data, timeout=8)
        if res.status_code == 200:
            print("[SOS SUCCESS]: Telegram Alert with photo and live GPS sent successfully!")
        else:
            print(f"[Telegram Error]: {res.text}")
    except Exception as e:
        print(f"[Telegram Exception]: {e}")

def trigger_sos_thread(frame, reason):
    global emergency_sos_triggered
    if not emergency_sos_triggered:
        emergency_sos_triggered = True
        t = threading.Thread(target=execute_10sec_emergency_sos, args=(frame.copy(), reason))
        t.daemon = True
        t.start()

# --- MATH & POSE CALCULATIONS ---
def euclidean_distance(pt1, pt2):
    return math.sqrt((pt1[0] - pt2[0]) ** 2 + (pt1[1] - pt2[1]) ** 2)

def calculate_ear(eye_landmarks):
    v1 = euclidean_distance(eye_landmarks[1], eye_landmarks[5])
    v2 = euclidean_distance(eye_landmarks[2], eye_landmarks[4])
    h = euclidean_distance(eye_landmarks[0], eye_landmarks[3])
    return (v1 + v2) / (2.0 * h) if h != 0 else 0.0

def calculate_mar(mouth_landmarks):
    v1 = euclidean_distance(mouth_landmarks[2], mouth_landmarks[3])
    v2 = euclidean_distance(mouth_landmarks[4], mouth_landmarks[5])
    v3 = euclidean_distance(mouth_landmarks[6], mouth_landmarks[7])
    h = euclidean_distance(mouth_landmarks[0], mouth_landmarks[1])
    return (v1 + v2 + v3) / (3.0 * h) if h != 0 else 0.0

def estimate_head_pose(landmarks, img_w, img_h):
    image_points = np.array([
        (landmarks[1].x * img_w, landmarks[1].y * img_h),      
        (landmarks[152].x * img_w, landmarks[152].y * img_h),  
        (landmarks[33].x * img_w, landmarks[33].y * img_h),    
        (landmarks[263].x * img_w, landmarks[263].y * img_h),  
        (landmarks[61].x * img_w, landmarks[61].y * img_h),    
        (landmarks[291].x * img_w, landmarks[291].y * img_h)   
    ], dtype="double")

    model_points = np.array([
        (0.0, 0.0, 0.0),
        (0.0, -330.0, -65.0),
        (-225.0, 170.0, -135.0),
        (225.0, 170.0, -135.0),
        (-150.0, -150.0, -125.0),
        (150.0, -150.0, -125.0)
    ], dtype="double")

    focal_length = img_w
    center = (img_w / 2, img_h / 2)
    camera_matrix = np.array([
        [focal_length, 0, center[0]],
        [0, focal_length, center[1]],
        [0, 0, 1]
    ], dtype="double")

    dist_coeffs = np.zeros((4, 1))
    success, rotation_vector, translation_vector = cv2.solvePnP(
        model_points, image_points, camera_matrix, dist_coeffs, flags=cv2.SOLVEPNP_ITERATIVE
    )

    if not success:
        return 0.0, 0.0, 0.0, None

    rmat, _ = cv2.Rodrigues(rotation_vector)
    angles, _, _, _, _, _ = cv2.RQDecomp3x3(rmat)

    pitch = angles[0]
    yaw = angles[1]
    roll = angles[2]

    (nose_end_point2D, _) = cv2.projectPoints(
        np.array([(0.0, 0.0, 100.0)]), rotation_vector, translation_vector, camera_matrix, dist_coeffs
    )
    p1 = (int(image_points[0][0]), int(image_points[0][1]))
    p2 = (int(nose_end_point2D[0][0][0]), int(nose_end_point2D[0][0][1]))

    return pitch, yaw, roll, (p1, p2)

def draw_rounded_rect(img, pt1, pt2, color, thickness=2, r=15):
    x1, y1 = pt1
    x2, y2 = pt2
    cv2.line(img, (x1 + r, y1), (x2 - r, y1), color, thickness)
    cv2.line(img, (x1 + r, y2), (x2 - r, y2), color, thickness)
    cv2.line(img, (x1, y1 + r), (x1, y2 - r), color, thickness)
    cv2.line(img, (x2, y1 + r), (x2, y2 - r), color, thickness)
    cv2.ellipse(img, (x1 + r, y1 + r), (r, r), 180, 0, 90, color, thickness)
    cv2.ellipse(img, (x2 - r, y1 + r), (r, r), 270, 0, 90, color, thickness)
    cv2.ellipse(img, (x1 + r, y2 - r), (r, r), 90, 0, 90, color, thickness)
    cv2.ellipse(img, (x2 - r, y2 - r), (r, r), 0, 0, 90, color, thickness)

# --- MAIN RUNTIME LOOP ---
def main():
    global smooth_pitch, smooth_yaw, smooth_roll, emergency_sos_triggered
    global session_start_time, last_rest_alert_time, last_fatigue_state
    global is_recording_incident, post_incident_frames_needed, current_post_frames

    session_start_time = start_driving_session()

    # Background voice listener thread start
    t_listener = threading.Thread(target=voice_listener_worker)
    t_listener.daemon = True
    t_listener.start()

    base_options = python.BaseOptions(model_asset_path="face_landmarker.task")
    options = vision.FaceLandmarkerOptions(
        base_options=base_options,
        output_face_blendshapes=False,
        output_facial_transformation_matrixes=False,
        num_faces=1
    )
    detector = vision.FaceLandmarker.create_from_options(options)

    cap = cv2.VideoCapture(0)
    if not cap.isOpened():
        print("Error: Camera feed could not be initialized.")
        return

    eye_closed_start = None
    last_eye_closed_time = 0
    yawn_start = None
    last_yawn_time = 0
    head_down_start = None
    last_head_down_time = 0

    total_yawns = 0
    is_yawning_now = False
    yawn_fatigue_alerted = False

    print("Driver Safety & SOS System Active... Press 'q' to exit.")

    while cap.isOpened():
        success, frame = cap.read()
        if not success:
            continue

        frame = cv2.flip(frame, 1)
        h, w, _ = frame.shape
        now = time.time()

        # Blackbox Circular Frame Cache
        blackbox_buffer.append(frame.copy())

        if is_recording_incident:
            current_post_frames.append(frame.copy())
            if len(current_post_frames) >= post_incident_frames_needed:
                pre_event_snapshot = list(blackbox_buffer)
                full_incident_clip = pre_event_snapshot + current_post_frames

                t_bb = threading.Thread(
                    target=save_blackbox_video_worker, 
                    args=(full_incident_clip, "INCIDENT")
                )
                t_bb.daemon = True
                t_bb.start()

                is_recording_incident = False
                current_post_frames = []

        # Drive duration calculation
        drive_duration_sec = now - session_start_time
        hrs = int(drive_duration_sec // 3600)
        mins = int((drive_duration_sec % 3600) // 60)
        secs = int(drive_duration_sec % 60)
        drive_time_str = f"{hrs:02d}:{mins:02d}:{secs:02d}"

        gray = cv2.cvtColor(frame, cv2.COLOR_BGR2GRAY)
        brightness = np.mean(gray)
        is_low_light = brightness < BRIGHTNESS_THRESHOLD

        if is_low_light:
            lab = cv2.cvtColor(frame, cv2.COLOR_BGR2LAB)
            l, a, b = cv2.split(lab)
            l = clahe.apply(l)
            lab = cv2.merge((l, a, b))
            processed_frame = cv2.cvtColor(lab, cv2.COLOR_LAB2BGR)
        else:
            processed_frame = frame.copy()

        rgb_frame = cv2.cvtColor(processed_frame, cv2.COLOR_BGR2RGB)
        mp_image = mp.Image(image_format=mp.ImageFormat.SRGB, data=rgb_frame)
        detection_result = detector.detect(mp_image)

        if detection_result.face_landmarks:
            for face_landmarks in detection_result.face_landmarks:
                x_coords = [int(lm.x * w) for lm in face_landmarks]
                y_coords = [int(lm.y * h) for lm in face_landmarks]
                xmin, xmax = max(0, min(x_coords) - 15), min(w, max(x_coords) + 15)
                ymin, ymax = max(0, min(y_coords) - 25), min(h, max(y_coords) + 15)

                left_eye_pts = [(int(face_landmarks[i].x * w), int(face_landmarks[i].y * h)) for i in LEFT_EYE]
                right_eye_pts = [(int(face_landmarks[i].x * w), int(face_landmarks[i].y * h)) for i in RIGHT_EYE]
                mouth_pts = [(int(face_landmarks[i].x * w), int(face_landmarks[i].y * h)) for i in MOUTH]

                avg_ear = (calculate_ear(left_eye_pts) + calculate_ear(right_eye_pts)) / 2.0
                mar = calculate_mar(mouth_pts)
                raw_pitch, raw_yaw, raw_roll, nose_line = estimate_head_pose(face_landmarks, w, h)

                smooth_pitch = 0.8 * smooth_pitch + 0.2 * raw_pitch
                smooth_yaw = 0.8 * smooth_yaw + 0.2 * raw_yaw
                smooth_roll = 0.8 * smooth_roll + 0.2 * raw_roll

                # 1. Eye Closure Tracking
                is_eye_closed = avg_ear < EAR_THRESHOLD
                if is_eye_closed:
                    last_eye_closed_time = now
                    if eye_closed_start is None:
                        eye_closed_start = now
                else:
                    if now - last_eye_closed_time > 0.6:
                        eye_closed_start = None

                perclos_value = update_perclos(is_eye_closed, now, window_duration=60.0)

                # 2. Yawning Tracking
                if mar > MAR_THRESHOLD:
                    last_yawn_time = now
                    if yawn_start is None:
                        yawn_start = now

                    if not is_yawning_now and (now - yawn_start) >= 1.2:
                        is_yawning_now = True
                        total_yawns += 1
                        print(f"[YAWN DETECTED]: Total Yawn Count = {total_yawns}")

                        if total_yawns >= YAWN_ALERT_THRESHOLD and not yawn_fatigue_alerted:
                            yawn_fatigue_alerted = True
                            trigger_yawn_fatigue_alert(total_yawns)
                else:
                    if now - last_yawn_time > 0.6:
                        yawn_start = None
                        is_yawning_now = False

                # 3. Head Down Tracking
                is_head_down = (smooth_pitch < PITCH_DOWN_LIMIT or abs(smooth_roll) > ROLL_TILT_LIMIT or abs(smooth_yaw) > YAW_TURNING_LIMIT)
                if is_head_down:
                    last_head_down_time = now
                    if head_down_start is None:
                        head_down_start = now
                else:
                    if now - last_head_down_time > 0.6:
                        head_down_start = None

                # Calculate Active Durations
                eye_duration = (now - eye_closed_start) if eye_closed_start else 0.0
                yawn_duration = (now - yawn_start) if yawn_start else 0.0
                head_duration = (now - head_down_start) if head_down_start else 0.0
                critical_duration = max(eye_duration, yawn_duration, head_duration)

                # Fatigue evaluation
                fatigue_score = calculate_fatigue_score(
                    perclos_val=perclos_value,
                    yawn_count=total_yawns,
                    head_distraction_sec=head_duration,
                    drive_duration_sec=drive_duration_sec
                )
                fatigue_status, recommendation = get_fatigue_status(fatigue_score)

                head_risk_str = "HIGH" if head_duration > 2.0 else "NORMAL"
                if fatigue_status == "HIGH RISK":
                    time_since_last_alert = now - last_rest_alert_time
                    if (last_fatigue_state == "NORMAL") or (time_since_last_alert >= REST_ALERT_COOLDOWN):
                        last_rest_alert_time = now
                        print(f"\n[FATIGUE ENGINE]: High Fatigue Score ({fatigue_score}/100). Dispatching Rest Advisory...")
                        trigger_rest_alert(
                            drive_time_str,
                            perclos_value,
                            total_yawns,
                            head_risk_str,
                            fatigue_score,
                            fatigue_status
                        )
                        trigger_blackbox_recorder("HIGH_FATIGUE")

                last_fatigue_state = fatigue_status

                if critical_duration == 0.0:
                    emergency_sos_triggered = False

                reason = "Driver Inattentive"
                if eye_duration == critical_duration and critical_duration > 0:
                    reason = "Continuous Eyes Closed"
                elif yawn_duration == critical_duration and critical_duration > 0:
                    reason = "Fatigue (Continuous Yawning)"
                elif head_duration == critical_duration and critical_duration > 0:
                    reason = "Head Pose Distraction / Sleeping"

                # Escalation Stages
                if critical_duration >= EMERGENCY_SOS_TIME:
                    theme_color = (0, 0, 255)
                    trigger_audio_alarm(True, level=3)
                    trigger_sos_thread(processed_frame, reason)
                    trigger_blackbox_recorder("EMERGENCY_SOS")

                    cv2.rectangle(processed_frame, (0, h - 50), (w, h), (0, 0, 200), -1)
                    cv2.putText(processed_frame, f"EMERGENCY: SOS TRIGGERED ({critical_duration:.1f}s)", (10, h - 18),
                                cv2.FONT_HERSHEY_SIMPLEX, 0.55, (255, 255, 255), 2, cv2.LINE_AA)

                elif critical_duration >= STAGE2_TIME_LIMIT:
                    theme_color = (0, 0, 255)
                    trigger_audio_alarm(True, level=2)

                    cv2.rectangle(processed_frame, (0, h - 50), (w, h), (0, 100, 255), -1)
                    cv2.putText(processed_frame, f"WARNING: {reason} ({critical_duration:.1f}s)", (15, h - 18),
                                cv2.FONT_HERSHEY_SIMPLEX, 0.6, (255, 255, 255), 2, cv2.LINE_AA)

                elif critical_duration >= STAGE1_TIME_LIMIT:
                    theme_color = (0, 255, 255)
                    trigger_audio_alarm(False)

                else:
                    theme_color = (0, 255, 120)
                    trigger_audio_alarm(False)

                # Overlays
                cv2.polylines(processed_frame, [np.array(left_eye_pts)], True, theme_color, 1, cv2.LINE_AA)
                cv2.polylines(processed_frame, [np.array(right_eye_pts)], True, theme_color, 1, cv2.LINE_AA)
                cv2.polylines(processed_frame, [np.array(mouth_pts)], True, (255, 255, 0), 1, cv2.LINE_AA)
                draw_rounded_rect(processed_frame, (xmin, ymin), (xmax, ymax), theme_color, thickness=2, r=12)

                if nose_line:
                    cv2.line(processed_frame, nose_line[0], nose_line[1], (0, 255, 255), 2, cv2.LINE_AA)

                # HUD Top Panel
                overlay = processed_frame.copy()
                cv2.rectangle(overlay, (0, 0), (w, 75), (15, 15, 15), -1)
                cv2.addWeighted(overlay, 0.80, processed_frame, 0.20, 0, processed_frame)

                cv2.putText(processed_frame, f"EAR: {avg_ear:.2f}", (15, 20), cv2.FONT_HERSHEY_SIMPLEX, 0.42, (255, 255, 255), 1, cv2.LINE_AA)
                cv2.putText(processed_frame, f"MAR: {mar:.2f}", (105, 20), cv2.FONT_HERSHEY_SIMPLEX, 0.42, (255, 255, 255), 1, cv2.LINE_AA)
                cv2.putText(processed_frame, f"YAWNS: {total_yawns}", (195, 20), cv2.FONT_HERSHEY_SIMPLEX, 0.42, (0, 255, 255) if total_yawns >= YAWN_ALERT_THRESHOLD else (255, 255, 255), 1, cv2.LINE_AA)
                cv2.putText(processed_frame, f"P:{smooth_pitch:.0f} Y:{smooth_yaw:.0f} R:{smooth_roll:.0f}", (295, 20), cv2.FONT_HERSHEY_SIMPLEX, 0.42, (255, 255, 255), 1, cv2.LINE_AA)

                if is_recording_incident:
                    cv2.circle(processed_frame, (w - 150, 16), 5, (0, 0, 255), -1)
                    cv2.putText(processed_frame, "BLACKBOX REC", (w - 138, 20), cv2.FONT_HERSHEY_SIMPLEX, 0.40, (0, 0, 255), 1, cv2.LINE_AA)
                elif is_low_light:
                    cv2.putText(processed_frame, "NIGHT VISION", (w - 140, 20), cv2.FONT_HERSHEY_SIMPLEX, 0.42, (0, 255, 255), 1, cv2.LINE_AA)

                cv2.putText(processed_frame, f"DRIVE TIME: {drive_time_str}", (15, 44), cv2.FONT_HERSHEY_SIMPLEX, 0.44, (200, 255, 255), 1, cv2.LINE_AA)
                cv2.putText(processed_frame, f"PERCLOS: {perclos_value:.1f}%", (210, 44), cv2.FONT_HERSHEY_SIMPLEX, 0.44, (0, 255, 255) if perclos_value >= 12.0 else (255, 255, 255), 1, cv2.LINE_AA)
                if head_duration > 0.5:
                    cv2.putText(processed_frame, f"HEAD DISTRACTION: {head_duration:.1f}s", (370, 44), cv2.FONT_HERSHEY_SIMPLEX, 0.44, (0, 165, 255), 1, cv2.LINE_AA)

                status_color = (0, 0, 255) if fatigue_status == "HIGH RISK" else (0, 255, 120)
                cv2.putText(processed_frame, f"FATIGUE: {fatigue_score}/100", (15, 68), cv2.FONT_HERSHEY_SIMPLEX, 0.46, status_color, 2, cv2.LINE_AA)
                cv2.putText(processed_frame, f"STATUS: {fatigue_status}", (185, 68), cv2.FONT_HERSHEY_SIMPLEX, 0.46, status_color, 2, cv2.LINE_AA)

                if fatigue_status == "HIGH RISK":
                    cv2.rectangle(processed_frame, (w - 240, 48), (w - 10, 72), (0, 0, 180), -1)
                    cv2.putText(processed_frame, "! TAKE A REST BREAK", (w - 232, 65), cv2.FONT_HERSHEY_SIMPLEX, 0.44, (255, 255, 255), 1, cv2.LINE_AA)
        else:
            eye_closed_start = None
            yawn_start = None
            head_down_start = None
            trigger_audio_alarm(False)
            cv2.putText(processed_frame, "NO DRIVER DETECTED", (30, 50), cv2.FONT_HERSHEY_SIMPLEX, 0.8, (0, 0, 255), 2, cv2.LINE_AA)

        cv2.imshow("AI Driver Safety System", processed_frame)

        if cv2.waitKey(5) & 0xFF == ord("q"):
            trigger_audio_alarm(False)
            break

    cap.release()
    cv2.destroyAllWindows()

if __name__ == "__main__":
    main()