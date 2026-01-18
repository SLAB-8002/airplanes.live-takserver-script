# This was a ATAK community script developed by https://github.com/niccellular
# Shout out WildFire and SLAB
import requests
import xml.etree.ElementTree as ET
import argparse
import socket
import struct
import datetime
import uuid
import time
import ssl
import csv
import os

def load_known_craft(csv_path):
    """
    Load known craft CSV into a dict keyed by lowercase HEX.
    Expected headers (case-insensitive): HEX, COT, ICON, CALLSIGN
    Extra headers are ignored. Missing columns are treated as blank.
    """
    mapping = {}
    if not csv_path:
        return mapping
    if not os.path.isfile(csv_path):
        raise FileNotFoundError(f"known_craft CSV not found: {csv_path}")

    with open(csv_path, newline='', encoding="utf-8") as f:
        reader = csv.DictReader(f)
        # Normalize fieldnames to upper for case-insensitive access
        fieldnames = [h.upper() for h in reader.fieldnames or []]
        # Fallbacks if unexpected headers
        def get(row, key):
            # case-insensitive lookup
            for k, v in row.items():
                if k.upper() == key:
                    return (v or "").strip()
            return ""

        for row in reader:
            hex_code = get(row, "HEX").lower()
            if not hex_code:
                continue
            mapping[hex_code] = {
                "COT": get(row, "COT"),
                "ICON": get(row, "ICON"),
                "CALLSIGN": get(row, "CALLSIGN"),
            }
    return mapping

def labelize_key(key: str) -> str:
    """
    Convert a JSON key into a human label.
    - short keys => ALL CAPS (e.g., hex -> HEX, r -> R)
    - longer keys => Title Case with spaces (e.g., alt_baro -> Alt Baro)
    """
    if not key:
        return ""
    k = str(key).strip()
    if len(k) <= 3:
        return k.upper()
    return k.replace("_", " ").strip().title()

TYPE_SOURCE_LABELS = {
    "adsb_icao": "ADS-B (ICAO)",
    "adsb_icao_nt": "ADS-B (ICAO, non-transponder)",
    "adsr_icao": "ADS-R (ICAO)",
    "tisb_icao": "TIS-B (ICAO)",
    "adsc": "ADS-C",
    "mlat": "MLAT",
    "other": "Other",
    "mode_s": "Mode S (no position)",
    "adsb_other": "ADS-B (non-ICAO)",
    "adsr_other": "ADS-R (non-ICAO)",
    "tisb_other": "TIS-B (non-ICAO)",
    "tisb_trackfile": "TIS-B (trackfile)",
}

def format_adsb_remarks(json_data: dict, known_callsign: str = "") -> str:
    """
    Build a human-readable multi-line remarks string with only:
    Flight Callsign, Registration, Hex, Source, Type, Description, Squawk
    """
    # Callsign: prefer known_callsign if present, else 'flight'
    callsign = (known_callsign or json_data.get("flight") or "").strip()

    registration = (json_data.get("r") or "").strip()
    hex_code = (json_data.get("hex") or "").strip().upper()
    ac_type = (json_data.get("t") or "").strip()
    desc = (json_data.get("desc") or "").strip()   # not always present
    ownop = (json_data.get("ownOp") or "").strip()
    src_code = (json_data.get("type") or "").strip()
    src_label = TYPE_SOURCE_LABELS.get(src_code, src_code or "")

    squawk = (json_data.get("squawk") or "").strip()

    fields = [
        ("Flight Callsign", callsign),
        ("Registration", registration),
        ("ICAO", hex_code),
        ("Type", ac_type),
        ("Description", desc),
        ("Operator",ownop),
        ("Source", src_label),
        ("Squawk", squawk),
    ]

    # Only emit lines that have a value
    lines = [f"{label}: {value}" for label, value in fields if value not in ("", None)]
    return "\n".join(lines)

def json_to_cot(json_data, stale_secs, known_map):
    """
    Convert one ADS-B JSON aircraft to CoT.
    known_map: dict keyed by lowercase hex -> {"COT","ICON","CALLSIGN"} (all strings; may be empty)
    """
    # Prepare time info
    cot_time = datetime.datetime.now(datetime.timezone.utc)
    stale = cot_time + datetime.timedelta(seconds=stale_secs)

    # Identify the aircraft
    hex_code = (json_data.get("hex", "") or "").lower()

    # Look up known craft overrides (if any)
    known = known_map.get(hex_code, {}) if known_map else {}
    known_cot = (known.get("COT") or "").strip()
    known_icon = (known.get("ICON") or "").strip()
    known_callsign = (known.get("CALLSIGN") or "").strip()

    # Derive the default CoT type (only if we don't have a known COT)
    ismil = json_data.get("dbFlags", 0) & 1
    category = (json_data.get("category", "") or "").lower()

    cot_type = None
    if known_cot:
        cot_type = known_cot
    else:
        # Original behavior: require a category to classify, otherwise skip
        if not category:
            return ""
        cot_type = "a"
        if ismil:
            # Label all mil as friendly
            cot_type += "-f"
        else:
            # Label all non-mil as neutral
            cot_type += "-n"

        # https://www.adsbexchange.com/emitter-category-ads-b-do-260b-2-2-3-2-5-2/
        if category[0] == "c":
            # C is for ground
            cot_type += "-G"
            if category == "c1" or category == "c2":
                #  C1 Surface vehicle – emergency vehicle
                #  C2 Surface vehicle – service vehicle
                cot_type += "-E-V"
                if not ismil:
                    cot_type += "-C"
                cot_type += "-U"
        else:
            cot_type += "-A"
            if ismil:
                cot_type += "-M"
            else:
                cot_type += "-C"

            if category == "a7":
                # helicopter
                cot_type += "-H"
            elif category[0] == "a":
                # rest of the A should be set to fixed wing
                cot_type += "-F"
            elif category == "b6":
                # Unmanned aerial vehicle
                cot_type += "-F-q"
            elif category == "b2":
                # Lighter than air
                cot_type += "-L"

    # Build CoT XML
    root = ET.Element("event")
    root.set("version", "2.0")
    root.set("uid", str(uuid.uuid3(uuid.NAMESPACE_DNS, json_data.get("hex", ""))))
    root.set("time", cot_time.strftime("%Y-%m-%dT%H:%M:%S.%fZ"))
    root.set("start", cot_time.strftime("%Y-%m-%dT%H:%M:%S.%fZ"))
    root.set("stale", stale.strftime("%Y-%m-%dT%H:%M:%S.%fZ"))
    root.set("type", cot_type)
    root.set("how", "m-g")
    
    detail = ET.SubElement(root, "detail")

    # contact/callsign logic: prefer CSV CALLSIGN if present, else fall back to flight
    callsign_value = known_callsign if known_callsign else json_data.get("flight", "") or ""
    callsign_value = callsign_value.strip()
    contact = ET.SubElement(detail, "contact")
    contact.set("callsign", callsign_value)
    contact.set("type", json_data.get("t", ""))

    # If ICON present, add <usericon path="..."/>
    if known_icon:
        usericon = ET.SubElement(detail, "usericon")
        usericon.set("iconsetpath", known_icon)

    remarks = ET.SubElement(detail, "remarks")
    remarks.set("source", "airplanes.live")
    remarks.text = format_adsb_remarks(json_data, known_callsign=known_callsign)
    
    track = ET.SubElement(detail, "track")
    # Fetch the ground speed in knots from the JSON data
    gs_knots = json_data.get("gs", 0)
    # Convert the ground speed to meters per second (1 knot = 0.514444 meters per second)
    gs_mps = float(gs_knots) * 0.514444
    track.set("speed", str(gs_mps))
    track.set("course", str(json_data.get("track", "0")))

    point = ET.SubElement(root, "point")
    point.set("lat", str(json_data.get("lat", "")))
    point.set("lon", str(json_data.get("lon", "")))
    
    # Fetch the barometric altitude in feet from the JSON data
    try:
        alt_baro_feet = float(json_data.get("alt_baro", 0))
    except (ValueError, TypeError):
        # might return "ground" or be missing
        alt_baro_feet = 0.0
    
    # Standard sea level pressure in hPa
    standard_sea_level_pressure = 1013.25
    
    # Fetch nav_qnh if available
    try:
        nav_qnh = float(json_data.get('nav_qnh', standard_sea_level_pressure))
    except (ValueError, TypeError):
        nav_qnh = standard_sea_level_pressure
    
    # Convert barometric altitude to pressure altitude
    pressure_altitude_feet = alt_baro_feet + 1000 * (standard_sea_level_pressure - nav_qnh) / 30
    
    # Convert pressure altitude from feet to meters
    pressure_altitude_meters = pressure_altitude_feet * 0.3048
    
    # Set the converted altitude to the 'hae' attribute
    point.set("hae", str(pressure_altitude_meters))
    
    point.set("ce", "9999999.0")
    point.set("le", "9999999.0")
    return ET.tostring(root, encoding="utf-8").decode("utf-8")

def fetch_json(_url):
    response = requests.get(_url)
    response.raise_for_status()
    return response.json()

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("-lat", type=float, required=True,
                        help="Centerpoint Latitude")
    parser.add_argument("-lon", type=float, required=True,
                        help="Centerpoint Longitude")
    parser.add_argument('--dest', required=True,
                        help='Destination Hostname or IP Address for Sending CoT')
    parser.add_argument('--port', required=True, type=int,
                        help='Destination Port')
    parser.add_argument('--radius', required=False, type=int, default=25,
                        help='Radius in Nautical Miles')
    parser.add_argument('--rate', required=False, type=int, default=0,
                        help='Rate at which to poll the server in seconds. Setting to 0 will run once and exit')
    parser.add_argument('--known-craft', required=False, default=None,
                        help='Path to known_craft.csv with headers: HEX,COT,ICON,CALLSIGN')
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--udp', required=False, action='store_true', default=False,
                        help='Send packets via UDP')
    group.add_argument('--tcp', required=False, action='store_true', default=False,
                        help='Send packets via TCP')
    group.add_argument('--cert', required=False,
                       help='Path to unencrypted User SSL Certificate')
    args = parser.parse_args()

    # Load known craft map (optional)
    try:
        known_map = load_known_craft(args.known_craft) if args.known_craft else {}
    except Exception as e:
        raise SystemExit(f"Failed to load --known-craft CSV: {e}")

    url = "https://api.airplanes.live/v2/point/" + str(args.lat) + "/" + str(args.lon) + "/" + str(args.radius)

    if args.rate <= 0:
        stale_period = 60
    else:
        stale_period = args.rate * 2.5

    if args.udp:
        tmp = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        tmp.connect(("8.8.8.8", 80))
        default_local_ip = tmp.getsockname()[0]
        tmp.close()
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM, socket.IPPROTO_UDP)
        s.bind(("", 0))
        s.setsockopt(socket.IPPROTO_IP, socket.IP_MULTICAST_IF, socket.inet_aton(default_local_ip))

        # This makes Winsock pick an interface/route
        s.connect((args.dest, args.port))
    elif args.tcp:
        s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        s.connect((args.dest, args.port))
    else:
        # Cert
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        s = ssl.wrap_socket(sock, certfile=args.cert)
        s.connect((args.dest, args.port))

    while True:
        json_data = fetch_json(url)
        if 'ac' in json_data:
            for aircraft in json_data['ac']:
                cot_xml = json_to_cot(aircraft, stale_period, known_map)
                if not cot_xml:
                    continue
                # print(cot_xml)
                if args.udp:
                    s.send(cot_xml.encode("utf-8"))
                else:
                    s.sendall(bytes(cot_xml, "utf-8"))
        if args.rate <= 0:
            break
        else:
            time.sleep(args.rate)
