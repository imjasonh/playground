//! Coordinates and Google encoded polylines.

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
}

/// Driving path plus optional Google-provided labels.
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
