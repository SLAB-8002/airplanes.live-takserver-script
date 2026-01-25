#!/usr/bin/env python3
# This was a ATAK community script developed by https://github.com/niccellular
# Shout out WildFire and SLAB

import requests
import xml.etree.ElementTree as ET
import argparse
import socket
import datetime
import uuid
import time
import ssl
import csv
import os
import sys
import unicodedata
import yaml
from pathlib import Path

def deep_get(d, keys, default=None):
    cur = d
    for k in keys:
        if not isinstance(cur, dict) or k not in cur:
            return default
        cur = cur[k]
    return cur

def load_yaml_config(path):
    if not path:
        return {}
    p = Path(path)
    if not p.exists():
        return {}
    with p.open("r", encoding="utf-8") as f:
        data = yaml.safe_load(f) or {}
    if not isinstance(data, dict):
        raise ValueError("config.yaml root must be a mapping/dict")
    return data

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

    with open(csv_path, newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)

        def get(row, key):
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

# Ordered MIL aircraft CoT classification rules.
# These ONLY apply when:
#   - known_craft.csv does not provide COT, AND
#   - the aircraft appears to be MIL (dbFlags bit 1), AND
#   - a matching rule is found
#
# Rules are evaluated in order; first match wins.
MIL_COT_RULES = [
    {"t": "C30J", "desc_has": ["KC-130"], "cot": "a-f-A-M-F-C"},
    {"t": "C30J", "desc_has": ["MC-130"], "cot": "a-f-A-M-F-M"},
    {"t": "C30J", "desc_has": ["HC-130"], "cot": "a-f-A-M-F-H"},
    {"t": "K35R", "cot": "a-f-A-M-F-K"},
    {"t": "C5M",  "cot": "a-f-A-M-F-C-H"},
    {"t": "C17",  "cot": "a-f-A-M-F-C"},
    {"t": "C27J", "cot": "a-f-A-M-F-C"},
    {"t": "C30J", "cot": "a-f-A-M-F-C"},
    {"t": "P8",   "cot": "a-f-A-M-F-P"},
    {"t": "AS65", "cot": "a-f-A-M-H-H"},
    {"t": "H47",  "cot": "a-f-A-M-H-C"},
    {"t": "H60",  "cot": "a-f-A-M-H-U"},
    {"t": "H64",  "cot": "a-f-A-M-H-A"},
]

_DASHES = {
    "\u2010",  # hyphen
    "\u2011",  # non-breaking hyphen
    "\u2012",  # figure dash
    "\u2013",  # en dash
    "\u2014",  # em dash
    "\u2212",  # minus sign
}

def _clean_text(s: str) -> str:
    """
    Normalize text for matching:
    - Unicode normalize
    - Convert weird dashes to ASCII '-'
    - Collapse whitespace
    - casefold for robust case-insensitive compare
    """
    s = unicodedata.normalize("NFKC", (s or "").strip())
    if any(d in s for d in _DASHES):
        for d in _DASHES:
            s = s.replace(d, "-")
    s = " ".join(s.split())
    return s.casefold()

def _clean_upper(s: str) -> str:
    s = unicodedata.normalize("NFKC", (s or "").strip())
    if any(d in s for d in _DASHES):
        for d in _DASHES:
            s = s.replace(d, "-")
    return s.upper()

def mil_cot_from_rules(json_data: dict) -> str:
    """
    First-match-wins against MIL_COT_RULES.
    Supports:
      - t exact match (case-insensitive)
      - desc_has: all substrings must appear in desc
      - ownop_has: all substrings must appear in ownOp
    """
    t = _clean_upper(json_data.get("t"))
    desc = _clean_text(json_data.get("desc"))
    ownop = _clean_text(json_data.get("ownOp"))

    for rule in MIL_COT_RULES:
        rt = _clean_upper(rule.get("t"))
        if rt and rt != t:
            continue

        # desc_has
        for sub in (rule.get("desc_has") or []):
            if _clean_text(sub) not in desc:
                break
        else:
            # ownop_has
            for sub in (rule.get("ownop_has") or rule.get("ownOp_has") or []):
                if _clean_text(sub) not in ownop:
                    break
            else:
                cot = (rule.get("cot") or "").strip()
                if cot:
                    return cot

    return ""

def format_adsb_remarks(json_data: dict, known_callsign: str = "") -> str:
    """
    Build a human-readable multi-line remarks string with only:
    Flight Callsign, Registration, Hex, Source, Type, Description, Squawk
    """
    callsign = (known_callsign or json_data.get("flight") or "").strip()
    registration = (json_data.get("r") or "").strip()
    hex_code = (json_data.get("hex") or "").strip().upper()
    ac_type = (json_data.get("t") or "").strip()
    desc = (json_data.get("desc") or "").strip()
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
        ("Operator", ownop),
        ("Source", src_label),
        ("Squawk", squawk),
    ]
    lines = [f"{label}: {value}" for label, value in fields if value not in ("", None)]
    return "\n".join(lines)

def json_to_cot(json_data, stale_secs, known_map):
    """
    Convert one ADS-B JSON aircraft to CoT.
    known_map: dict keyed by lowercase hex -> {"COT","ICON","CALLSIGN"} (all strings; may be empty)
    """
    cot_time = datetime.datetime.now(datetime.timezone.utc)
    stale = cot_time + datetime.timedelta(seconds=stale_secs)

    hex_code = (json_data.get("hex", "") or "").lower()

    known = known_map.get(hex_code, {}) if known_map else {}
    known_cot = (known.get("COT") or "").strip()
    known_icon = (known.get("ICON") or "").strip()
    known_callsign = (known.get("CALLSIGN") or "").strip()

    ismil = json_data.get("dbFlags", 0) & 1
    category = (json_data.get("category", "") or "").lower()

    cot_type = None
    if known_cot:
        cot_type = known_cot
    else:
        # NEW: ordered MIL rules (only for MIL, only if known_craft didn't override)
        if ismil:
            mil_rule_cot = mil_cot_from_rules(json_data)
            if mil_rule_cot:
                cot_type = mil_rule_cot

        # Fallback to original category-based behavior if no MIL rule matched
        if not cot_type:
            # Original behavior: require a category to classify, otherwise skip
            if not category:
                return ""
            cot_type = "a"
            if ismil:
                cot_type += "-f"
            else:
                cot_type += "-n"

            # https://www.adsbexchange.com/emitter-category-ads-b-do-260b-2-2-3-2-5-2/
            if category[0] == "c":
                cot_type += "-G"
                if category == "c1" or category == "c2":
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
                    cot_type += "-H"
                elif category[0] == "a":
                    cot_type += "-F"
                elif category == "b6":
                    cot_type += "-F-q"
                elif category == "b2":
                    cot_type += "-L"

    root = ET.Element("event")
    root.set("version", "2.0")
    root.set("uid", str(uuid.uuid3(uuid.NAMESPACE_DNS, json_data.get("hex", ""))))
    root.set("time", cot_time.strftime("%Y-%m-%dT%H:%M:%S.%fZ"))
    root.set("start", cot_time.strftime("%Y-%m-%dT%H:%M:%S.%fZ"))
    root.set("stale", stale.strftime("%Y-%m-%dT%H:%M:%S.%fZ"))
    root.set("type", cot_type)
    root.set("how", "m-g")

    detail = ET.SubElement(root, "detail")

    callsign_value = known_callsign if known_callsign else json_data.get("flight", "") or ""
    callsign_value = callsign_value.strip()
    contact = ET.SubElement(detail, "contact")
    contact.set("callsign", callsign_value)
    contact.set("type", json_data.get("t", ""))

    if known_icon:
        usericon = ET.SubElement(detail, "usericon")
        usericon.set("iconsetpath", known_icon)

    remarks = ET.SubElement(detail, "remarks")
    remarks.set("source", "airplanes.live")
    remarks.text = format_adsb_remarks(json_data, known_callsign=known_callsign)

    track = ET.SubElement(detail, "track")
    gs_knots = json_data.get("gs", 0)
    gs_mps = float(gs_knots) * 0.514444
    track.set("speed", str(gs_mps))
    track.set("course", str(json_data.get("track", "0")))

    point = ET.SubElement(root, "point")
    point.set("lat", str(json_data.get("lat", "")))
    point.set("lon", str(json_data.get("lon", "")))

    try:
        alt_baro_feet = float(json_data.get("alt_baro", 0))
    except (ValueError, TypeError):
        alt_baro_feet = 0.0

    standard_sea_level_pressure = 1013.25
    try:
        nav_qnh = float(json_data.get("nav_qnh", standard_sea_level_pressure))
    except (ValueError, TypeError):
        nav_qnh = standard_sea_level_pressure

    pressure_altitude_feet = alt_baro_feet + 1000 * (standard_sea_level_pressure - nav_qnh) / 30
    pressure_altitude_meters = pressure_altitude_feet * 0.3048
    point.set("hae", str(pressure_altitude_meters))

    point.set("ce", "9999999.0")
    point.set("le", "9999999.0")

    return ET.tostring(root, encoding="utf-8").decode("utf-8")


def fetch_json(_url):
    # Avoid hanging forever when running as a service
    headers = {"User-Agent": "adsb-to-tak/1.0"}
    response = requests.get(_url, headers=headers, timeout=10)
    response.raise_for_status()
    return response.json()

def connect_socket(args):
    """
    Preserve original socket behavior:
    - UDP: set IP_MULTICAST_IF based on default route IP; connect() so send() works
    - TCP: plain TCP
    - CERT: ssl.wrap_socket with certfile
    """
    if args.udp:
        tmp = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        tmp.connect(("8.8.8.8", 80))
        default_local_ip = tmp.getsockname()[0]
        tmp.close()

        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM, socket.IPPROTO_UDP)
        s.bind(("", 0))
        s.setsockopt(socket.IPPROTO_IP, socket.IP_MULTICAST_IF, socket.inet_aton(default_local_ip))

        # This makes Winsock pick an interface/route (kept from original logic)
        s.connect((args.dest, args.port))
        return s

    if args.tcp:
        s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        s.connect((args.dest, args.port))
        return s

    # Cert-wrapped TCP
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    s = ssl.wrap_socket(sock, certfile=args.cert)
    s.connect((args.dest, args.port))
    return s

if __name__ == "__main__":
    parser = argparse.ArgumentParser()

    # Optional config.yaml for defaults (keeps existing CLI logic intact)
    parser.add_argument(
        "--config",
        required=False,
        default=None,
        help="Path to config.yaml (optional). Values act as defaults for CLI args.",
    )

    # Keep flags/names the same to preserve existing usage
    parser.add_argument("-lat", type=float, required=False, help="Centerpoint Latitude")
    parser.add_argument("-lon", type=float, required=False, help="Centerpoint Longitude")
    parser.add_argument("--dest", required=False, help="Destination Hostname or IP Address for Sending CoT")
    parser.add_argument("--port", required=False, type=int, help="Destination Port")
    parser.add_argument("--radius", required=False, type=int, default=25, help="Radius in Nautical Miles")
    parser.add_argument(
        "--rate",
        required=False,
        type=int,
        default=0,
        help="Rate at which to poll the server in seconds. Setting to 0 will run once and exit",
    )
    parser.add_argument(
        "--known-craft",
        required=False,
        default=None,
        help="Path to known_craft.csv with headers: HEX,COT,ICON,CALLSIGN",
    )

    # Transport: keep original mutually-exclusive options, but make it not-required so config.yaml can supply it.
    group = parser.add_mutually_exclusive_group(required=False)
    group.add_argument("--udp", required=False, action="store_true", default=False, help="Send packets via UDP")
    group.add_argument("--tcp", required=False, action="store_true", default=False, help="Send packets via TCP")
    group.add_argument("--cert", required=False, help="Path to unencrypted User SSL Certificate")

    args = parser.parse_args()

    # Load config.yaml if provided
    cfg = {}
    if args.config:
        try:
            cfg = load_yaml_config(args.config)
        except Exception as e:
            raise SystemExit(f"Failed to load --config YAML: {e}")

    # Apply config values only if CLI didn't supply them (or left them at default)
    def apply_cfg(attr, keys, *, when):
        cur = getattr(args, attr)
        if when(cur):
            v = deep_get(cfg, keys, None)
            if v is not None:
                setattr(args, attr, v)

    apply_cfg("lat", ["filter", "lat"], when=lambda v: v is None)
    apply_cfg("lon", ["filter", "lon"], when=lambda v: v is None)
    apply_cfg("dest", ["tak", "host"], when=lambda v: not v)
    apply_cfg("port", ["tak", "port"], when=lambda v: v is None)
    apply_cfg("radius", ["filter", "radius_nm"], when=lambda v: v == 25)
    apply_cfg("rate", ["poll", "rate_sec"], when=lambda v: v == 0)
    apply_cfg("known_craft", ["known_craft", "path"], when=lambda v: v is None)

    # Transport selection from config if none provided on CLI
    if not (args.udp or args.tcp or args.cert):
        mode = (deep_get(cfg, ["tak", "mode"], "") or "").strip().lower()
        if mode == "udp":
            args.udp = True
        elif mode == "tcp":
            args.tcp = True
        elif mode == "cert":
            cert_path = deep_get(cfg, ["tak", "cert"], None)
            if cert_path:
                args.cert = cert_path

    # Enforce original "required" semantics after config merge
    missing = []
    if args.lat is None:
        missing.append("lat")
    if args.lon is None:
        missing.append("lon")
    if not args.dest:
        missing.append("dest")
    if args.port is None:
        missing.append("port")
    if missing:
        raise SystemExit("Missing required settings: " + ", ".join(missing) + " (provide via CLI or --config)")

    if not (args.udp or args.tcp or args.cert):
        raise SystemExit("Missing transport: choose one of --udp/--tcp/--cert (or set tak.mode in --config)")

    # Load known craft map (optional)
    try:
        known_map = load_known_craft(args.known_craft) if args.known_craft else {}
    except Exception as e:
        raise SystemExit(f"Failed to load --known-craft CSV: {e}")

    # KEEP existing URL logic (hardcoded format)
    url = "https://api.airplanes.live/v2/point/" + str(args.lat) + "/" + str(args.lon) + "/" + str(args.radius)

    # KEEP existing stale logic
    if args.rate <= 0:
        stale_period = 60
    else:
        stale_period = args.rate * 2.5

    # Connect initial socket
    s = connect_socket(args)

    # Main loop (minimal robustness: reconnect on errors)
    while True:
        try:
            json_data = fetch_json(url)
            if "ac" in json_data:
                for aircraft in json_data["ac"]:
                    cot_xml = json_to_cot(aircraft, stale_period, known_map)
                    if not cot_xml:
                        continue
                    if args.udp:
                        s.send(cot_xml.encode("utf-8"))
                    else:
                        s.sendall(cot_xml.encode("utf-8"))
        except KeyboardInterrupt:
            break
        except Exception as e:
            print(f"[ERROR] {e}", file=sys.stderr)
            try:
                s.close()
            except Exception:
                pass
            time.sleep(2)
            try:
                s = connect_socket(args)
            except Exception as e2:
                print(f"[ERROR] reconnect failed: {e2}", file=sys.stderr)
                time.sleep(5)

        if args.rate <= 0:
            break
        else:
            time.sleep(args.rate)