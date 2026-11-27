#!/usr/bin/env python3
"""
Fetch Public Domain Natural Earth 50m GeoJSON for North America (US + Southern Canada),
project with USGS Albers Equal-Area Conic onto the Rails hex lattice coordinate space,
simplify cleanly with Douglas-Peucker, and write `maps/na_geo.json`.
"""
import json
import math
import os
import urllib.request

BASE = "https://raw.githubusercontent.com/nvkelso/natural-earth-vector/master/geojson"
URLS = {
    "countries": f"{BASE}/ne_50m_admin_0_countries.geojson",
    "lakes": f"{BASE}/ne_50m_lakes.geojson",
    "rivers": f"{BASE}/ne_50m_rivers_lake_centerlines.geojson",
    "states": f"{BASE}/ne_50m_admin_1_states_provinces_lines.geojson",
}

# USGS Albers Equal-Area Conic for North America
LON0 = math.radians(-96.0)
LAT0 = math.radians(39.0)
PHI1 = math.radians(29.5)
PHI2 = math.radians(45.5)

N = 0.5 * (math.sin(PHI1) + math.sin(PHI2))
C = math.cos(PHI1) ** 2 + 2.0 * N * math.sin(PHI1)
RHO0 = math.sqrt(C - 2.0 * N * math.sin(LAT0)) / N

# Map box in projected Albers units -> lattice space [1.5 .. 46.5] x [1.2 .. 28.0]
# Lattice width = 48.0, height = 29.0 (approx 46 cols x 32 rows hex lattice)
WORLD_W = 48.0
WORLD_H = 29.0


def albers_raw(lon_deg, lat_deg):
    lam = math.radians(lon_deg)
    phi = math.radians(lat_deg)
    theta = N * (lam - LON0)
    rho = math.sqrt(max(1e-12, C - 2.0 * N * math.sin(phi))) / N
    x = rho * math.sin(theta)
    y = RHO0 - rho * math.cos(theta)
    return x, y


# Compute bounding box of continental US + Southern Canada (lat 24.5..51.5, lon -125..-63)
CORNERS = [
    (-125.0, 50.5),
    (-63.0, 50.5),
    (-125.0, 24.5),
    (-63.0, 24.5),
    (-96.0, 51.5),
    (-96.0, 24.5),
]
RAW_XS = [albers_raw(lo, la)[0] for lo, la in CORNERS]
RAW_YS = [albers_raw(lo, la)[1] for lo, la in CORNERS]
MIN_X, MAX_X = min(RAW_XS), max(RAW_XS)
MIN_Y, MAX_Y = min(RAW_YS), max(RAW_YS)

PAD_X, PAD_Y = 1.6, 1.4
SCALE = min((WORLD_W - 2 * PAD_X) / (MAX_X - MIN_X), (WORLD_H - 2 * PAD_Y) / (MAX_Y - MIN_Y))
OFF_X = (WORLD_W - (MAX_X - MIN_X) * SCALE) / 2.0
OFF_Y = (WORLD_H - (MAX_Y - MIN_Y) * SCALE) / 2.0


def project(lon, lat):
    rx, ry = albers_raw(lon, lat)
    x = (rx - MIN_X) * SCALE + OFF_X
    # Flip Y so North is up (smaller y)
    y = (MAX_Y - ry) * SCALE + OFF_Y
    return [round(x, 3), round(y, 3)]


def dp_simplify(pts, eps):
    if len(pts) <= 2:
        return pts
    ax, ay = pts[0]
    bx, by = pts[-1]
    dx, dy = bx - ax, by - ay
    denom = dx * dx + dy * dy
    max_d2 = -1.0
    idx = 0
    for i in range(1, len(pts) - 1):
        px, py = pts[i]
        if denom < 1e-12:
            d2 = (px - ax) ** 2 + (py - ay) ** 2
        else:
            t = max(0.0, min(1.0, ((px - ax) * dx + (py - ay) * dy) / denom))
            cx, cy = ax + t * dx, ay + t * dy
            d2 = (px - cx) ** 2 + (py - cy) ** 2
        if d2 > max_d2:
            max_d2 = d2
            idx = i
    if max_d2 > eps * eps:
        left = dp_simplify(pts[: idx + 1], eps)
        right = dp_simplify(pts[idx:], eps)
        return left[:-1] + right
    return [pts[0], pts[-1]]


def clip_poly_top(poly, min_y):
    """Sutherland-Hodgman clip against y >= min_y (cuts off northern Canada cleanly at top of board)."""
    if not poly:
        return []
    out = []
    n = len(poly)
    for i in range(n):
        a = poly[i]
        b = poly[(i + 1) % n]
        a_in = a[1] >= min_y
        b_in = b[1] >= min_y
        if a_in and b_in:
            out.append(b)
        elif a_in and not b_in:
            t = (min_y - a[1]) / (b[1] - a[1] + 1e-12)
            out.append([round(a[0] + t * (b[0] - a[0]), 3), round(min_y, 3)])
        elif not a_in and b_in:
            t = (min_y - a[1]) / (b[1] - a[1] + 1e-12)
            out.append([round(a[0] + t * (b[0] - a[0]), 3), round(min_y, 3)])
            out.append(b)
    return out


def poly_area(poly):
    if len(poly) < 3:
        return 0.0
    a = 0.0
    for i in range(len(poly)):
        x1, y1 = poly[i]
        x2, y2 = poly[(i + 1) % len(poly)]
        a += x1 * y2 - x2 * y1
    return abs(a) * 0.5


def fetch_json(url):
    print(f"Fetching {url} ...")
    with urllib.request.urlopen(url, timeout=20) as r:
        return json.loads(r.read().decode("utf-8"))


def iter_polygons(geom):
    if geom["type"] == "Polygon":
        yield geom["coordinates"][0]
    elif geom["type"] == "MultiPolygon":
        for poly in geom["coordinates"]:
            yield poly[0]


def iter_lines(geom):
    if geom["type"] == "LineString":
        yield geom["coordinates"]
    elif geom["type"] == "MultiLineString":
        for line in geom["coordinates"]:
            yield line


def main():
    countries = fetch_json(URLS["countries"])
    lakes = fetch_json(URLS["lakes"])
    rivers = fetch_json(URLS["rivers"])
    states = fetch_json(URLS["states"])

    # Clip northern Canada around y = 1.6 (roughly 52°N, just north of Calgary/Winnipeg/Quebec)
    TOP_Y = 1.6
    # Land polygons: US contiguous + Southern Canada (including Vancouver Island, Nova Scotia, Cape Breton, PEI, Long Island)
    land_polygons = []
    us_canada_border_polys = []
    for feat in countries["features"]:
        iso = feat["properties"].get("ISO_A3") or feat["properties"].get("ADM0_A3")
        if iso not in ("USA", "CAN"):
            continue
        for ring in iter_polygons(feat["geometry"]):
            # Filter out Alaska, Hawaii, Arctic islands by rough lon/lat centroid/bounds
            lons = [p[0] for p in ring]
            lats = [p[1] for p in ring]
            if max(lons) < -132.0 or min(lons) > -58.0 or max(lats) < 23.0 or min(lats) > 54.5:
                continue
            proj = [project(lo, la) for lo, la in ring]
            clipped = clip_poly_top(proj, TOP_Y)
            if len(clipped) < 3:
                continue
            simp = dp_simplify(clipped, 0.09)
            if len(simp) >= 3 and poly_area(simp) >= 0.45:
                land_polygons.append(simp)
                if iso == "USA":
                    us_canada_border_polys.append(simp)

    # Great Lakes + Lake Winnipeg + Great Salt Lake
    KEEP_LAKES = {
        "Lake Superior",
        "Lake Michigan",
        "Lake Huron",
        "Lake Erie",
        "Lake Ontario",
        "Lake Winnipeg",
        "Great Salt Lake",
        "Lake St. Clair",
    }
    lake_polygons = []
    for feat in lakes["features"]:
        name = feat["properties"].get("name") or ""
        if name not in KEEP_LAKES:
            continue
        for ring in iter_polygons(feat["geometry"]):
            proj = [project(lo, la) for lo, la in ring]
            clipped = clip_poly_top(proj, TOP_Y)
            simp = dp_simplify(clipped, 0.06)
            if len(simp) >= 3 and poly_area(simp) >= 0.06:
                lake_polygons.append(simp)

    # Major North American rivers for both visuals and +$2M bridge crossings
    KEEP_RIVERS = {
        "Mississippi": "Mississippi",
        "Missouri": "Missouri",
        "Ohio": "Ohio",
        "Colorado": "Colorado",
        "Columbia": "Columbia",
        "Rio Grande": "Rio Grande",
        "St. Lawrence": "St. Lawrence",
        "Saint Lawrence": "St. Lawrence",
        "Arkansas": "Arkansas",
        "Red": "Red",
        "Snake": "Columbia",
        "Saskatchewan": "Saskatchewan",
        "South Saskatchewan": "Saskatchewan",
        "Ottawa": "St. Lawrence",
        "Tennessee": "Ohio",
    }
    river_lines = []
    for feat in rivers["features"]:
        name = (feat["properties"].get("name") or "").strip()
        canonical = None
        for key, val in KEEP_RIVERS.items():
            if name == key or name.startswith(key + " "):
                canonical = val
                break
        if not canonical:
            continue
        for line in iter_lines(feat["geometry"]):
            pts = [project(lo, la) for lo, la in line if -130 <= lo <= -60 and 24 <= la <= 53]
            pts = [p for p in pts if p[1] >= TOP_Y]
            if len(pts) < 2:
                continue
            simp = dp_simplify(pts, 0.09)
            if len(simp) >= 2:
                river_lines.append({"name": canonical, "points": simp})

    # State & province internal borders (subtle cartographic context!)
    borders = []
    for feat in states["features"]:
        iso = feat["properties"].get("ADM0_A3") or ""
        if iso not in ("USA", "CAN"):
            continue
        for line in iter_lines(feat["geometry"]):
            pts = [project(lo, la) for lo, la in line if -126 <= lo <= -60 and 24.5 <= la <= 52]
            pts = [p for p in pts if p[1] >= TOP_Y]
            if len(pts) < 2:
                continue
            simp = dp_simplify(pts, 0.12)
            if len(simp) >= 2:
                borders.append({"name": iso, "points": simp})

    # Real lat/lon coordinates for classic US + Southern Canada Empire Builder cities!
    CITY_COORDS = {
        # 6 Major Cities
        "new_york": (-74.006, 40.713),
        "chicago": (-87.630, 41.878),
        "toronto": (-79.383, 43.653),
        "new_orleans": (-90.072, 29.951),
        "los_angeles": (-118.244, 34.052),
        "san_francisco": (-122.419, 37.775),
        # Northeast & Eastern Canada
        "boston": (-71.059, 42.360),
        "montreal": (-73.567, 45.502),
        "quebec": (-71.208, 46.814),
        "philadelphia": (-75.165, 39.953),
        "washington": (-77.037, 38.907),
        "pittsburgh": (-79.996, 40.441),
        "buffalo": (-78.878, 42.886),
        "detroit": (-83.046, 42.331),
        "cleveland": (-81.694, 41.499),
        "cincinnati": (-84.512, 39.103),
        # Southeast
        "norfolk": (-76.286, 36.851),
        "raleigh": (-78.638, 35.779),
        "charlotte": (-80.843, 35.227),
        "atlanta": (-84.388, 33.749),
        "birmingham": (-86.802, 33.519),
        "jacksonville": (-81.656, 30.332),
        "tampa": (-82.457, 27.951),
        "miami": (-80.192, 25.762),
        # Midwest, Plains & Central Canada
        "minneapolis": (-93.265, 44.978),
        "duluth": (-92.100, 46.787),
        "winnipeg": (-97.138, 49.895),
        "st_louis": (-90.199, 38.627),
        "memphis": (-90.049, 35.150),
        "kansas_city": (-94.579, 39.100),
        "omaha": (-95.935, 41.257),
        "oklahoma_city": (-97.516, 35.468),
        "dallas": (-96.797, 32.777),
        "houston": (-95.370, 29.760),
        "san_antonio": (-98.494, 29.424),
        # West, Mountains & Western Canada
        "calgary": (-114.072, 51.045),
        "vancouver": (-123.121, 49.283),
        "seattle": (-122.332, 47.606),
        "portland": (-122.676, 45.515),
        "boise": (-116.202, 43.615),
        "salt_lake": (-111.891, 40.761),
        "denver": (-104.990, 39.739),
        "las_vegas": (-115.140, 36.170),
        "phoenix": (-112.074, 33.448),
        "albuquerque": (-106.650, 35.084),
        "el_paso": (-106.485, 31.762),
    }

    city_points = {cid: project(lo, la) for cid, (lo, la) in CITY_COORDS.items()}

    out = {
        "width": WORLD_W,
        "height": WORLD_H,
        "land_polygons": land_polygons,
        "lake_polygons": lake_polygons,
        "rivers": river_lines,
        "borders": borders,
        "city_points": city_points,
    }

    out_path = os.path.join(os.path.dirname(__file__), "..", "maps", "na_geo.json")
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    with open(out_path, "w") as f:
        json.dump(out, f, separators=(",", ":"))
    size = os.path.getsize(out_path)
    print(
        f"Wrote {out_path} ({size:,} bytes): "
        f"{len(land_polygons)} land polys, {len(lake_polygons)} lakes, "
        f"{len(river_lines)} rivers, {len(borders)} border lines, {len(city_points)} cities"
    )


if __name__ == "__main__":
    main()
