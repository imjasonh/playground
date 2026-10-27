#!/usr/bin/env python3
"""Generate examples/subway/data_*.ne from the MTA subway GTFS feed.

Usage:

    python3 gen_data.py GTFS_DIR STATIONS_JSON OUT_DIR

GTFS_DIR holds the static subway feed, either as the `.txt` files from
https://rrgtfsfeeds.s3.amazonaws.com/gtfs_subway.zip or as the `.json`
files of the `mta-gtfs-static` npm package. STATIONS_JSON is the MTA
"Subway Stations" dataset (the `stations.json` of the
`mta-subway-stations` npm package), which adds the complex, structure,
borough, and platform direction labels that GTFS doesn't carry.

The game models weekday daytime service. For each route and direction
it keeps the stop patterns that run at least a quarter of the trips
that start between 10:00 and 15:00, with the median running time to
each stop and the mean headway over those five hours.

Times are in game ticks of 30 seconds.
"""

import csv
import json
import os
import statistics
import sys
from collections import Counter, defaultdict

DAY_START = 10 * 3600
# Train motion: cruise speed in pixels a frame, and frames to reach it.
CRUISE = 8
ACCEL_FRAMES = 220
# The game starts at noon.
START_TICK = 12 * 3600 // 30
DAY_END = 15 * 3600
TICK = 30

# Route id -> (glyph, color group). Groups pick the bullet colors.
ROUTES = [
    ("1", "1", "red"), ("2", "2", "red"), ("3", "3", "red"),
    ("4", "4", "green"), ("5", "5", "green"), ("6", "6", "green"),
    ("7", "7", "purple"),
    ("A", "A", "blue"), ("C", "C", "blue"), ("E", "E", "blue"),
    ("B", "B", "orange"), ("D", "D", "orange"), ("F", "F", "orange"),
    ("M", "M", "orange"),
    ("G", "G", "lime"),
    ("J", "J", "brown"), ("Z", "Z", "brown"),
    ("L", "L", "gray"),
    ("N", "N", "yellow"), ("Q", "Q", "yellow"), ("R", "R", "yellow"),
    ("W", "W", "yellow"),
    ("GS", "S", "shuttle"), ("FS", "S", "shuttle"), ("H", "S", "shuttle"),
]
ROUTE_INDEX = {r[0]: i for i, r in enumerate(ROUTES)}
# Express variants merge into their route; SIR isn't reachable by subway.
ROUTE_ALIAS = {"6X": "6", "7X": "7", "FX": "F"}
# Station dataset route names for the shuttles.
STATION_ROUTE = {"S": None}

COLOR_GROUPS = ["red", "green", "purple", "blue", "orange", "lime",
                "brown", "gray", "yellow", "shuttle"]

CHARSET = (" ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
           "0123456789-./&'():,!>")
CHAR_CODE = {c: i for i, c in enumerate(CHARSET)}

NAME_MAX = 28

ABBREVIATIONS = [
    ("Sutphin Blvd-Archer Av-JFK Airport", "Sutphin Blvd-Archer Av-JFK"),
    ("42 St-Port Authority Bus Terminal", "42 St-Port Authority"),
    ("81 St-Museum of Natural History", "81 St-Museum of Nat History"),
    ("Bedford Park Blvd-Lehman College", "Bedford Pk Blvd-Lehman Coll"),
    ("Franklin Av-Medgar Evers College", "Franklin Av-Medgar Evers"),
    ("President St-Medgar Evers College", "President St-Medgar Evers"),
    ("Middle Village-Metropolitan Av", "Middle Village-Metropolitan"),
    ("Jamaica Center-Parsons/Archer", "Jamaica Ctr-Parsons/Archer"),
]


def read_table(gtfs_dir, name):
    """Yield the rows of one GTFS table as dicts."""
    txt = os.path.join(gtfs_dir, name + ".txt")
    if os.path.exists(txt):
        with open(txt, newline="", encoding="utf-8-sig") as f:
            yield from csv.DictReader(f)
        return
    path = os.path.join(gtfs_dir, name + ".json")
    with open(path, encoding="utf-8") as f:
        # One record per line keeps the 80 MB stop_times file streaming.
        for line in f:
            line = line.strip().rstrip(",")
            if line.startswith("{"):
                yield json.loads(line)


def seconds(hms):
    h, m, s = hms.split(":")
    return int(h) * 3600 + int(m) * 60 + int(s)


def short_name(name):
    for long, short in ABBREVIATIONS:
        if name == long:
            name = short
    if len(name) > NAME_MAX:
        raise SystemExit(f"station name too long, add an abbreviation: {name}")
    for c in name:
        if c not in CHAR_CODE:
            raise SystemExit(f"character {c!r} in {name!r} is not in the font")
    return name


def encode(text):
    return [CHAR_CODE[c] for c in text]


def main():
    gtfs_dir, stations_json, out_dir = sys.argv[1:4]

    stops = {r["stop_id"]: r for r in read_table(gtfs_dir, "stops")}
    with open(stations_json, encoding="utf-8") as f:
        station_rows = json.load(f)

    # Stations: one per GTFS parent stop, in the dataset's order.
    stations = []
    by_stop = {}
    for row in station_rows:
        sid = row["GTFS Stop ID"]
        if sid not in stops or row["Borough"] == "SI":
            continue
        by_stop[sid] = len(stations)
        stations.append(row)

    weekday = {r["service_id"] for r in read_table(gtfs_dir, "calendar")
               if all(r[d] == "1" for d in
                      ("monday", "tuesday", "wednesday", "thursday", "friday"))}

    trips = {}
    for r in read_table(gtfs_dir, "trips"):
        route = ROUTE_ALIAS.get(r["route_id"], r["route_id"])
        if r["service_id"] in weekday and route in ROUTE_INDEX:
            trips[r["trip_id"]] = route

    trip_stops = defaultdict(list)
    for r in read_table(gtfs_dir, "stop_times"):
        if r["trip_id"] in trips:
            trip_stops[r["trip_id"]].append(
                (int(r["stop_sequence"]), r["stop_id"], seconds(r["arrival_time"])))

    # (route, direction letter) -> pattern tuple -> list of (start, times)
    groups = defaultdict(lambda: defaultdict(list))
    for trip_id, rows in trip_stops.items():
        rows.sort()
        start = rows[0][2]
        if not DAY_START <= start < DAY_END:
            continue
        direction = rows[0][1][-1]
        seq = tuple(r[1][:-1] for r in rows)
        if any(s not in by_stop for s in seq):
            continue
        times = [r[2] - start for r in rows]
        groups[(trips[trip_id], direction)][seq].append((start, times))

    patterns = []
    for (route, direction), pats in sorted(
            groups.items(), key=lambda kv: (ROUTE_INDEX[kv[0][0]], kv[0][1])):
        total = sum(len(v) for v in pats.values())
        ranked = sorted(pats.items(), key=lambda kv: -len(kv[1]))
        for seq, runs in ranked[:2]:
            if len(runs) * 4 < total or len(seq) < 2:
                continue
            cum = []
            for k in range(len(seq)):
                t = statistics.median(r[1][k] for r in runs)
                cum.append(round(t / TICK))
            for k in range(1, len(cum)):
                cum[k] = max(cum[k], cum[k - 1] + 2)
            headway = max(4, round((DAY_END - DAY_START) / TICK / len(runs)))
            first = min(r[0] for r in runs)
            phase = round(first / TICK) % headway
            if cum[-1] > 255:
                raise SystemExit(f"{route}{direction} runs longer than 255 ticks")
            patterns.append({
                "route": route, "dir": direction, "stops": seq, "cum": cum,
                "headway": headway, "phase": phase, "trips": len(runs),
            })

    # Platforms: which pattern stops serve each station direction.
    serve = defaultdict(list)
    for p, pat in enumerate(patterns):
        for k, sid in enumerate(pat["stops"][:-1]):
            serve[(by_stop[sid], pat["dir"])].append((p, k))

    # Direction labels.
    labels = []
    label_index = {}

    def label(text):
        text = text.replace(" - ", "-")
        if text not in label_index:
            label_index[text] = len(labels)
            labels.append(text)
        return label_index[text]

    label("")
    complexes = defaultdict(list)
    for i, row in enumerate(stations):
        complexes[row["Complex ID"]].append(i)

    names = []
    for row in stations:
        names.append(short_name(stops[row["GTFS Stop ID"]]["stop_name"]))

    # Map projection for the pause screen: 160 x 224 pixel area.
    lats = [float(r["GTFS Latitude"]) for r in stations]
    lons = [float(r["GTFS Longitude"]) for r in stations]
    lat0, lat1 = min(lats), max(lats)
    lon0, lon1 = min(lons), max(lons)
    kx = 0.7581  # cos(40.7 degrees)
    width_km = (lon1 - lon0) * kx
    height_km = lat1 - lat0
    scale = min(150 / width_km, 216 / height_km)
    off_x = (160 - width_km * scale) / 2 + 4
    off_y = (224 - height_km * scale) / 2 + 4

    def project(lat, lon):
        x = (lon - lon0) * kx * scale + off_x
        y = (lat1 - lat) * scale + off_y
        return round(x), round(y)

    out = []
    w = out.append
    w("// Generated by examples/subway/tools/gen_data.py from the MTA")
    w("// weekday subway GTFS feed and the MTA Subway Stations dataset.")
    w("// Do not edit by hand.")
    w("")

    n = len(stations)
    st = {k: [] for k in ("name_lo", "name_hi", "name_len", "flags", "map_x",
                          "map_y", "next_lo", "next_hi", "lab_n", "lab_s",
                          "rte_off_lo", "rte_off_hi", "rte_len", "srv_off_lo",
                          "srv_off_hi", "srv_n", "srv_s")}
    blob = []
    rte_list = []
    srv_pat = []
    srv_idx = []
    boroughs = {"M": 0, "Bx": 1, "Bk": 2, "Q": 3}
    for i, row in enumerate(stations):
        name = encode(names[i])
        st["name_lo"].append(len(blob) & 0xFF)
        st["name_hi"].append(len(blob) >> 8)
        st["name_len"].append(len(name))
        blob.extend(name)
        outdoor = 0 if row["Structure"] == "Subway" else 1
        st["flags"].append(outdoor | (boroughs[row["Borough"]] << 1))
        x, y = project(float(row["GTFS Latitude"]), float(row["GTFS Longitude"]))
        st["map_x"].append(x)
        st["map_y"].append(y)
        ring = complexes[row["Complex ID"]]
        nxt = ring[(ring.index(i) + 1) % len(ring)]
        st["next_lo"].append(nxt & 0xFF)
        st["next_hi"].append(nxt >> 8)
        st["lab_n"].append(label(row["North Direction Label"]))
        st["lab_s"].append(label(row["South Direction Label"]))
        routes = []
        for r in row["Daytime Routes"]:
            r = str(r)
            if r == "S":
                # The dataset names every shuttle S. Use the one that
                # stops here.
                for p in patterns:
                    if p["route"] in ("GS", "FS", "H") and row["GTFS Stop ID"] in p["stops"]:
                        r = p["route"]
                        break
            if r in ROUTE_INDEX and ROUTE_INDEX[r] not in routes:
                routes.append(ROUTE_INDEX[r])
        st["rte_off_lo"].append(len(rte_list) & 0xFF)
        st["rte_off_hi"].append(len(rte_list) >> 8)
        st["rte_len"].append(len(routes))
        rte_list.extend(routes)
        st["srv_off_lo"].append(len(srv_pat) & 0xFF)
        st["srv_off_hi"].append(len(srv_pat) >> 8)
        for d, key in (("N", "srv_n"), ("S", "srv_s")):
            entries = serve.get((i, d), [])
            st[key].append(len(entries))
            for p, k in entries:
                srv_pat.append(p)
                srv_idx.append(k)

    label_blob = []
    lab_lo, lab_hi, lab_len = [], [], []
    for text in labels:
        code = encode(text[:NAME_MAX])
        lab_lo.append(len(label_blob) & 0xFF)
        lab_hi.append(len(label_blob) >> 8)
        lab_len.append(len(code))
        label_blob.extend(code)

    pat = {k: [] for k in ("route", "dir", "head", "pc0", "len", "off_lo",
                           "off_hi", "dest_lo", "dest_hi")}
    ps_lo, ps_hi, ps_cum, ps_mod = [], [], [], []
    for p in patterns:
        pat["route"].append(ROUTE_INDEX[p["route"]])
        pat["dir"].append(0 if p["dir"] == "N" else 1)
        pat["head"].append(p["headway"])
        # Ticks since the last departure from the first stop, at the
        # game's start time.
        pat["pc0"].append((START_TICK - p["phase"]) % p["headway"])
        pat["len"].append(len(p["stops"]))
        pat["off_lo"].append(len(ps_lo) & 0xFF)
        pat["off_hi"].append(len(ps_lo) >> 8)
        dest = by_stop[p["stops"][-1]]
        pat["dest_lo"].append(dest & 0xFF)
        pat["dest_hi"].append(dest >> 8)
        for sid, c in zip(p["stops"], p["cum"]):
            s = by_stop[sid]
            ps_lo.append(s & 0xFF)
            ps_hi.append(s >> 8)
            ps_cum.append(c)
            ps_mod.append(c % p["headway"])

    # Distance in pixels a train covers in its first f frames from a
    # stop, accelerating evenly to CRUISE pixels a frame over
    # ACCEL_FRAMES frames. Braking runs the same table backward.
    acc = [round(CRUISE * f * f / (2 * ACCEL_FRAMES)) for f in range(ACCEL_FRAMES + 1)]

    def table(name, values):
        if not values:
            values = [0]
        rows = []
        for i in range(0, len(values), 16):
            rows.append("    " + ", ".join(str(v) for v in values[i:i + 16]))
        return f"const {name}: u8[{len(values)}] = [\n" + ",\n".join(rows) + "\n]"

    w(f"const NUM_STATIONS: u16 = {n}")
    w(f"const NUM_PATTERNS: u8 = {len(patterns)}")
    w(f"const NUM_ROUTES: u8 = {len(ROUTES)}")
    w(f"const CRUISE: u8 = {CRUISE}")
    w(f"const ACCEL_FRAMES: u8 = {ACCEL_FRAMES}")
    w(f"const ACCEL_DIST: u16 = {acc[-1]}")
    w("")
    for i, p in enumerate(patterns):
        dest = names[by_stop[p["stops"][-1]]]
        w(f"// pattern {i}: {p['route']} {p['dir']} to {dest}, {len(p['stops'])} stops,"
          f" {p['cum'][-1] * TICK // 60} min, every {p['headway'] * TICK / 60:g} min")
    w("")
    sections = {
        "stations": [
            table("ST_NAME_LO", st["name_lo"]), table("ST_NAME_HI", st["name_hi"]),
            table("ST_NAME_LEN", st["name_len"]), table("NAME_TEXT", blob),
            table("ST_FLAGS", st["flags"]), table("ST_NEXT_LO", st["next_lo"]),
            table("ST_NEXT_HI", st["next_hi"]), table("ST_LAB_N", st["lab_n"]),
            table("ST_LAB_S", st["lab_s"]), table("LAB_LO", lab_lo),
            table("LAB_HI", lab_hi), table("LAB_LEN", lab_len),
            table("LAB_TEXT", label_blob), table("ST_RTE_LO", st["rte_off_lo"]),
            table("ST_RTE_HI", st["rte_off_hi"]), table("ST_RTE_LEN", st["rte_len"]),
            table("RTE_LIST", rte_list), table("ST_MAP_X", st["map_x"]),
            table("ST_MAP_Y", st["map_y"]),
        ],
        "lines": [
            table("ST_SRV_LO", st["srv_off_lo"]), table("ST_SRV_HI", st["srv_off_hi"]),
            table("ST_SRV_N", st["srv_n"]), table("ST_SRV_S", st["srv_s"]),
            table("SRV_PAT", srv_pat), table("SRV_IDX", srv_idx),
            table("PAT_ROUTE", pat["route"]), table("PAT_DIR", pat["dir"]),
            table("PAT_HEAD", pat["head"]), table("PAT_PC0", pat["pc0"]),
            table("PAT_LEN", pat["len"]), table("PAT_OFF_LO", pat["off_lo"]),
            table("PAT_OFF_HI", pat["off_hi"]), table("PAT_DEST_LO", pat["dest_lo"]),
            table("PAT_DEST_HI", pat["dest_hi"]), table("PS_ST_LO", ps_lo),
            table("PS_ST_HI", ps_hi), table("PS_CUM", ps_cum), table("PS_MOD", ps_mod),
            table("ACC_LO", [a & 0xFF for a in acc]), table("ACC_HI", [a >> 8 for a in acc]),
        ],
    }
    with open(os.path.join(out_dir, "data_header.ne"), "w", encoding="utf-8") as f:
        f.write("\n".join(out) + "\n")
    for section, tables in sections.items():
        path = os.path.join(out_dir, f"data_{section}.ne")
        with open(path, "w", encoding="utf-8") as f:
            f.write(out[0] + "\n" + out[1] + "\n" + out[2] + "\n\n")
            f.write("\n\n".join(tables) + "\n")

    sizes = {s: sum(t.count(",") + 1 for t in ts) for s, ts in sections.items()}
    print(f"{n} stations, {len(patterns)} patterns, {len(ps_lo)} pattern stops,"
          f" {len(labels)} labels, bytes {sizes}", file=sys.stderr)
    for code in ("srv_n", "srv_s"):
        print(code, "max", max(st[code]), file=sys.stderr)


if __name__ == "__main__":
    main()
