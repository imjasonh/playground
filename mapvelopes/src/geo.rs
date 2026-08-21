//! Coordinates, Google encoded polylines, and the schematic geocoder.

use crate::address::Address;

/// WGS84 point.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct LatLng {
    pub lat: f64,
    pub lng: f64,
}

impl LatLng {
    pub fn new(lat: f64, lng: f64) -> Self {
        Self { lat, lng }
    }

    fn distance_deg(self, other: Self) -> f64 {
        let dlat = self.lat - other.lat;
        let dlng = self.lng - other.lng;
        (dlat * dlat + dlng * dlng).sqrt()
    }
}

/// Inclusive geographic bounding box.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Bounds {
    pub south: f64,
    pub west: f64,
    pub north: f64,
    pub east: f64,
}

impl Bounds {
    /// Bounding box of `points`, padded and given a minimum span so a short
    /// hop still fills the envelope.
    pub fn for_points(points: &[LatLng]) -> Self {
        let mut south = f64::INFINITY;
        let mut west = f64::INFINITY;
        let mut north = f64::NEG_INFINITY;
        let mut east = f64::NEG_INFINITY;
        for p in points {
            south = south.min(p.lat);
            north = north.max(p.lat);
            west = west.min(p.lng);
            east = east.max(p.lng);
        }
        if !south.is_finite() {
            return Bounds {
                south: 24.0,
                west: -125.0,
                north: 49.0,
                east: -66.0,
            };
        }
        let mut dlat = (north - south).max(0.04);
        let mut dlng = (east - west).max(0.04);
        // Keep roughly the envelope aspect so the route is not a thin ribbon.
        const ASPECT: f64 = 9.5 / 4.125;
        if dlng / dlat < ASPECT {
            dlng = dlat * ASPECT;
        } else {
            dlat = dlng / ASPECT;
        }
        let pad_lat = dlat * 0.18;
        let pad_lng = dlng * 0.18;
        let clat = (south + north) / 2.0;
        let clng = (west + east) / 2.0;
        Bounds {
            south: clat - dlat / 2.0 - pad_lat,
            north: clat + dlat / 2.0 + pad_lat,
            west: clng - dlng / 2.0 - pad_lng,
            east: clng + dlng / 2.0 + pad_lng,
        }
    }

    /// Project a point into PDF user space. `y` grows up, like PDF and latitude.
    pub fn project(self, p: LatLng, page_w: f32, page_h: f32) -> (f32, f32) {
        let x = ((p.lng - self.west) / (self.east - self.west)) as f32;
        let y0 = mercator_y(self.south);
        let y1 = mercator_y(self.north);
        let y = ((mercator_y(p.lat) - y0) / (y1 - y0)) as f32;
        (x.clamp(0.0, 1.0) * page_w, y.clamp(0.0, 1.0) * page_h)
    }
}

fn mercator_y(lat: f64) -> f64 {
    let lat = lat.clamp(-85.0, 85.0).to_radians();
    (std::f64::consts::FRAC_PI_4 + lat / 2.0).tan().ln()
}

/// Driving (or schematic) path plus optional Google-provided labels.
#[derive(Debug, Clone, PartialEq)]
pub struct Route {
    pub points: Vec<LatLng>,
    pub distance_text: Option<String>,
    pub duration_text: Option<String>,
}

impl Route {
    pub fn start(&self) -> Option<LatLng> {
        self.points.first().copied()
    }

    pub fn end(&self) -> Option<LatLng> {
        self.points.last().copied()
    }

    /// Great-circle miles along the polyline, used when Google did not send a distance.
    pub fn path_miles(&self) -> f64 {
        self.points
            .windows(2)
            .map(|w| haversine_miles(w[0], w[1]))
            .sum()
    }
}

/// Statute miles between two points.
pub fn haversine_miles(a: LatLng, b: LatLng) -> f64 {
    const R: f64 = 3958.8;
    let dlat = (b.lat - a.lat).to_radians();
    let dlng = (b.lng - a.lng).to_radians();
    let la1 = a.lat.to_radians();
    let la2 = b.lat.to_radians();
    let h = (dlat / 2.0).sin().powi(2) + la1.cos() * la2.cos() * (dlng / 2.0).sin().powi(2);
    2.0 * R * h.sqrt().asin()
}

/// Format a mile count the way a legend on an envelope can hold.
pub fn format_miles(miles: f64) -> String {
    if miles < 0.15 {
        "under a mile".to_string()
    } else if miles < 10.0 {
        format!("{miles:.1} miles")
    } else {
        format!("{:.0} miles", miles.round())
    }
}

/// Decode a Google encoded polyline into points.
pub fn decode_polyline(enc: &str) -> Vec<LatLng> {
    let bytes = enc.as_bytes();
    let mut i = 0;
    let mut lat: i32 = 0;
    let mut lng: i32 = 0;
    let mut out = Vec::new();
    while i < bytes.len() {
        let (dlat, ni) = decode_delta(bytes, i);
        i = ni;
        let (dlng, ni) = decode_delta(bytes, i);
        i = ni;
        lat += dlat;
        lng += dlng;
        out.push(LatLng {
            lat: lat as f64 * 1e-5,
            lng: lng as f64 * 1e-5,
        });
    }
    out
}

/// Encode points as a Google encoded polyline.
pub fn encode_polyline(points: &[LatLng]) -> String {
    let mut last_lat: i32 = 0;
    let mut last_lng: i32 = 0;
    let mut out = String::new();
    for p in points {
        let lat = (p.lat * 1e5).round() as i32;
        let lng = (p.lng * 1e5).round() as i32;
        encode_delta(&mut out, lat - last_lat);
        encode_delta(&mut out, lng - last_lng);
        last_lat = lat;
        last_lng = lng;
    }
    out
}

fn decode_delta(bytes: &[u8], mut i: usize) -> (i32, usize) {
    let mut result: i32 = 0;
    let mut shift = 0;
    loop {
        if i >= bytes.len() {
            return (0, i);
        }
        let b = bytes[i] as i32 - 63;
        i += 1;
        result |= (b & 0x1f) << shift;
        shift += 5;
        if b < 0x20 {
            break;
        }
    }
    let delta = if result & 1 != 0 {
        !(result >> 1)
    } else {
        result >> 1
    };
    (delta, i)
}

fn encode_delta(out: &mut String, delta: i32) {
    // Cast first so a negative delta does not hit debug-overflow on `<<`.
    let mut v = (delta as u32) << 1;
    if delta < 0 {
        v = !v;
    }
    while v >= 0x20 {
        out.push(char::from(((v & 0x1f) | 0x20) as u8 + 63));
        v >>= 5;
    }
    out.push(char::from(v as u8 + 63));
}

/// Keep the first and last point and a roughly even sample in between so a
/// Static Maps URL stays under typical length limits.
pub fn subsample(points: &[LatLng], max: usize) -> Vec<LatLng> {
    if points.len() <= max || max < 2 {
        return points.to_vec();
    }
    let last = points.len() - 1;
    let step = last as f64 / (max - 1) as f64;
    (0..max)
        .map(|i| {
            let idx = ((i as f64) * step).round() as usize;
            points[idx.min(last)]
        })
        .collect()
}

/// Well-known places for the no-key geocoder. Longer names win when several match.
const PLACES: &[(&str, f64, f64)] = &[
    ("mountain view", 37.3861, -122.0839),
    ("cupertino", 37.3230, -122.0322),
    ("san francisco", 37.7749, -122.4194),
    ("los angeles", 34.0522, -118.2437),
    ("new york", 40.7128, -74.0060),
    ("brooklyn", 40.6782, -73.9442),
    ("chicago", 41.8781, -87.6298),
    ("seattle", 47.6062, -122.3321),
    ("boston", 42.3601, -71.0589),
    ("austin", 30.2672, -97.7431),
    ("denver", 39.7392, -104.9903),
    ("miami", 25.7617, -80.1918),
    ("portland", 45.5152, -122.6784),
    ("washington", 38.9072, -77.0369),
    ("atlanta", 33.7490, -84.3880),
    ("phoenix", 33.4484, -112.0740),
    ("philadelphia", 39.9526, -75.1652),
    ("london", 51.5074, -0.1278),
    ("paris", 48.8566, 2.3522),
    ("tokyo", 35.6762, 139.6503),
];

/// Geocode without a network: explicit `lat,lng`, then the gazetteer, then a
/// stable hash into the continental US.
pub fn geocode_stub(text: &str) -> LatLng {
    if let Some(ll) = parse_coords(text) {
        return ll;
    }
    for line in text.lines().rev() {
        if let Some(ll) = parse_coords(line) {
            return ll;
        }
    }
    let lower = text.to_lowercase();
    let mut best: Option<(&str, LatLng)> = None;
    for (name, lat, lng) in PLACES {
        if lower.contains(name) && best.map(|(n, _)| name.len() > n.len()).unwrap_or(true) {
            best = Some((*name, LatLng::new(*lat, *lng)));
        }
    }
    best.map(|(_, ll)| ll)
        .unwrap_or_else(|| hash_latlng(&lower))
}

fn parse_coords(text: &str) -> Option<LatLng> {
    let t = text.trim();
    let mut parts = t.split(',');
    let a = parts.next()?.trim().parse::<f64>().ok()?;
    let b = parts.next()?.trim().parse::<f64>().ok()?;
    if parts.next().is_some() {
        return None;
    }
    if (-90.0..=90.0).contains(&a) && (-180.0..=180.0).contains(&b) {
        Some(LatLng::new(a, b))
    } else {
        None
    }
}

fn hash_latlng(s: &str) -> LatLng {
    let h = fnv1a(s);
    let lat = 25.0 + ((h % 10_000) as f64 / 10_000.0) * 23.0;
    let lng = -124.0 + (((h / 10_000) % 10_000) as f64 / 10_000.0) * 56.0;
    LatLng::new(lat, lng)
}

pub(crate) fn fnv1a(s: &str) -> u64 {
    let mut h = 0xcbf29ce484222325;
    for b in s.as_bytes() {
        h ^= u64::from(*b);
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

/// A wiggly interpolation so a stub route looks like a road, not a ruler.
pub fn stub_route(from: LatLng, to: LatLng, seed: u64) -> Vec<LatLng> {
    let n = 20usize;
    let mut rng = SplitMix64::new(seed | 1);
    let span = from.distance_deg(to).max(0.25);
    let mut pts = Vec::with_capacity(n);
    for i in 0..n {
        let t = i as f64 / (n - 1) as f64;
        let lat = from.lat + (to.lat - from.lat) * t;
        let lng = from.lng + (to.lng - from.lng) * t;
        let wobble = (t * std::f64::consts::PI).sin();
        let amp = 0.07 * span;
        let nx = -(to.lat - from.lat);
        let ny = to.lng - from.lng;
        let len = (nx * nx + ny * ny).sqrt().max(1e-6);
        let jitter = (rng.f64() - 0.5) * 0.4;
        pts.push(LatLng::new(
            lat + (nx / len) * wobble * amp * (1.0 + jitter),
            lng + (ny / len) * wobble * amp * (1.0 + jitter),
        ));
    }
    pts[0] = from;
    pts[n - 1] = to;
    pts
}

/// Build a schematic [`Route`] for two addresses.
pub fn schematic_route(from: &Address, to: &Address) -> Route {
    let start = geocode_stub(&from.geocode_query());
    let end = geocode_stub(&to.geocode_query());
    let seed = fnv1a(&format!("{}|{}", from.geocode_query(), to.geocode_query()));
    let points = stub_route(start, end, seed);
    let miles = points.windows(2).map(|w| haversine_miles(w[0], w[1])).sum();
    Route {
        points,
        distance_text: Some(format!("about {}", format_miles(miles))),
        duration_text: None,
    }
}

struct SplitMix64(u64);

impl SplitMix64 {
    fn new(seed: u64) -> Self {
        Self(seed)
    }

    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }

    fn f64(&mut self) -> f64 {
        (self.next() >> 11) as f64 / ((1u64 << 53) as f64)
    }
}

/// Seeded RNG used by the schematic map so a given pair of addresses is stable.
pub(crate) fn map_rng(from: &Address, to: &Address) -> impl RngF32 {
    SplitMix64::new(fnv1a(&format!(
        "map|{}|{}",
        from.geocode_query(),
        to.geocode_query()
    )))
}

pub(crate) trait RngF32 {
    fn range(&mut self, a: f32, b: f32) -> f32;
}

impl RngF32 for SplitMix64 {
    fn range(&mut self, a: f32, b: f32) -> f32 {
        a + (b - a) * self.f64() as f32
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn polyline_roundtrip() {
        let pts = [
            LatLng::new(37.3861, -122.0839),
            LatLng::new(37.4419, -122.1430),
            LatLng::new(37.7749, -122.4194),
        ];
        let enc = encode_polyline(&pts);
        let got = decode_polyline(&enc);
        assert_eq!(got.len(), pts.len());
        for (a, b) in pts.iter().zip(&got) {
            assert!((a.lat - b.lat).abs() < 1e-5);
            assert!((a.lng - b.lng).abs() < 1e-5);
        }
    }

    #[test]
    fn gazetteer_picks_longest_match() {
        let ll = geocode_stub("Alice\n1600 Amphitheatre Parkway\nMountain View, CA 94043");
        assert!((ll.lat - 37.3861).abs() < 0.01);
        assert!((ll.lng + 122.0839).abs() < 0.01);
    }

    #[test]
    fn coords_line_wins() {
        let ll = geocode_stub("Somewhere\n40.7,-74.0");
        assert!((ll.lat - 40.7).abs() < 1e-9);
        assert!((ll.lng + 74.0).abs() < 1e-9);
    }

    #[test]
    fn stub_route_is_deterministic() {
        let a = Address::parse("Mountain View, CA").unwrap();
        let b = Address::parse("New York, NY").unwrap();
        let r1 = schematic_route(&a, &b);
        let r2 = schematic_route(&a, &b);
        assert_eq!(r1.points, r2.points);
        assert!(r1.points.len() >= 2);
        assert_ne!(r1.points.first(), r1.points.last());
    }

    #[test]
    fn subsample_keeps_ends() {
        let pts: Vec<_> = (0..100)
            .map(|i| LatLng::new(i as f64 * 0.01, i as f64 * 0.02))
            .collect();
        let s = subsample(&pts, 10);
        assert_eq!(s.len(), 10);
        assert_eq!(s[0], pts[0]);
        assert_eq!(s[9], pts[99]);
    }
}
