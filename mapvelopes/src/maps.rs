//! Google Maps URL builders, JSON parsers, and envelope-spec assembly.

use serde::Deserialize;
use url::Url;

use crate::address::Address;
use crate::error::Error;
use crate::geo::{decode_polyline, encode_polyline, format_miles, subsample, LatLng, Route};

/// Everything [`crate::render::render`] needs to draw one envelope.
#[derive(Debug, Clone)]
pub struct EnvelopeSpec {
    pub from: Address,
    pub to: Address,
    pub route: Option<Route>,
    pub map_jpeg: Option<Vec<u8>>,
}

impl EnvelopeSpec {
    /// Addresses only. No Maps calls, no background image.
    pub fn no_map(from: Address, to: Address) -> Self {
        EnvelopeSpec {
            from,
            to,
            route: None,
            map_jpeg: None,
        }
    }
}

/// True when `key` should be sent to Google. Empty strings and the
/// `REPLACE_…` / `stub` placeholders are treated as unset.
pub fn api_key_usable(key: Option<&str>) -> bool {
    match key.map(str::trim) {
        None | Some("") => false,
        Some("stub") | Some("STUB") => false,
        Some(k) if k.starts_with("REPLACE_") => false,
        Some(_) => true,
    }
}

/// Geocoding request for one address.
pub fn geocode_url(address: &str, key: &str) -> String {
    let mut url = Url::parse("https://maps.googleapis.com/maps/api/geocode/json")
        .expect("static geocode URL");
    url.query_pairs_mut()
        .append_pair("address", address)
        .append_pair("key", key);
    url.to_string()
}

/// Directions request between two already-geocoded points.
pub fn directions_url(from: LatLng, to: LatLng, key: &str) -> String {
    let mut url = Url::parse("https://maps.googleapis.com/maps/api/directions/json")
        .expect("static directions URL");
    url.query_pairs_mut()
        .append_pair("origin", &format_ll(from))
        .append_pair("destination", &format_ll(to))
        .append_pair("mode", "driving")
        .append_pair("key", key);
    url.to_string()
}

/// Static Maps request: route polyline plus start/end markers. JPEG, #10 aspect.
pub fn static_map_url(route: &Route, key: &str) -> String {
    let mut url =
        Url::parse("https://maps.googleapis.com/maps/api/staticmap").expect("static map URL");
    let pts = subsample(&route.points, 80);
    let enc = encode_polyline(&pts);
    let path = format!("weight:5|color:0x1A73E8ff|enc:{enc}");
    {
        let mut q = url.query_pairs_mut();
        q.append_pair("size", "640x276");
        q.append_pair("scale", "2");
        q.append_pair("maptype", "roadmap");
        q.append_pair("format", "jpg");
        q.append_pair("path", &path);
        if let Some(start) = route.start() {
            q.append_pair(
                "markers",
                &format!("color:0x34A853|size:mid|{}", format_ll(start)),
            );
        }
        if let Some(end) = route.end() {
            q.append_pair(
                "markers",
                &format!("color:0xEA4335|size:mid|{}", format_ll(end)),
            );
        }
        q.append_pair("key", key);
    }
    url.to_string()
}

fn format_ll(p: LatLng) -> String {
    format!("{:.6},{:.6}", p.lat, p.lng)
}

#[derive(Debug, Deserialize)]
struct StatusBody {
    status: String,
    #[serde(default)]
    error_message: Option<String>,
}

#[derive(Debug, Deserialize)]
struct GeocodeBody {
    status: String,
    #[serde(default)]
    error_message: Option<String>,
    #[serde(default)]
    results: Vec<GeocodeResult>,
}

#[derive(Debug, Deserialize)]
struct GeocodeResult {
    geometry: GeocodeGeometry,
}

#[derive(Debug, Deserialize)]
struct GeocodeGeometry {
    location: GeoPoint,
}

#[derive(Debug, Deserialize)]
struct GeoPoint {
    lat: f64,
    lng: f64,
}

#[derive(Debug, Deserialize)]
struct DirectionsBody {
    status: String,
    #[serde(default)]
    error_message: Option<String>,
    #[serde(default)]
    routes: Vec<DirectionsRoute>,
}

#[derive(Debug, Deserialize)]
struct DirectionsRoute {
    overview_polyline: EncodedLine,
    #[serde(default)]
    legs: Vec<DirectionsLeg>,
}

#[derive(Debug, Deserialize)]
struct EncodedLine {
    points: String,
}

#[derive(Debug, Deserialize)]
struct DirectionsLeg {
    #[serde(default)]
    distance: Option<TextValue>,
    #[serde(default)]
    duration: Option<TextValue>,
}

#[derive(Debug, Deserialize)]
struct TextValue {
    text: String,
    #[serde(default)]
    value: f64,
}

fn maps_status_error(kind: &str, status: &str, message: Option<&str>) -> Error {
    match message {
        Some(m) if !m.is_empty() => Error::Maps(format!("{kind}: {status}: {m}")),
        _ => Error::Maps(format!("{kind}: {status}")),
    }
}

/// Parse a Geocoding API body. The first result's location is used.
pub fn parse_geocode(body: &[u8]) -> Result<LatLng, Error> {
    let parsed: GeocodeBody =
        serde_json::from_slice(body).map_err(|e| Error::Maps(format!("geocode JSON: {e}")))?;
    if parsed.status != "OK" {
        return Err(maps_status_error(
            "geocode",
            &parsed.status,
            parsed.error_message.as_deref(),
        ));
    }
    let loc = &parsed
        .results
        .first()
        .ok_or_else(|| Error::Maps("geocode: OK but no results".into()))?
        .geometry
        .location;
    Ok(LatLng::new(loc.lat, loc.lng))
}

/// Parse a Directions API body.
pub fn parse_directions(body: &[u8]) -> Result<Route, Error> {
    let parsed: DirectionsBody =
        serde_json::from_slice(body).map_err(|e| Error::Maps(format!("directions JSON: {e}")))?;
    if parsed.status != "OK" {
        return Err(maps_status_error(
            "directions",
            &parsed.status,
            parsed.error_message.as_deref(),
        ));
    }
    let route = parsed
        .routes
        .first()
        .ok_or_else(|| Error::Maps("directions: OK but no routes".into()))?;
    let points = decode_polyline(&route.overview_polyline.points);
    if points.len() < 2 {
        return Err(Error::Maps("directions: polyline too short".into()));
    }
    let meters: f64 = route
        .legs
        .iter()
        .filter_map(|leg| leg.distance.as_ref().map(|d| d.value))
        .sum();
    let seconds: f64 = route
        .legs
        .iter()
        .filter_map(|leg| leg.duration.as_ref().map(|d| d.value))
        .sum();
    let distance_text = if meters > 0.0 {
        Some(format_miles(meters / 1609.344))
    } else {
        route
            .legs
            .first()
            .and_then(|leg| leg.distance.as_ref().map(|d| d.text.clone()))
    };
    let duration_text = if seconds > 0.0 {
        Some(format_duration(seconds as u64))
    } else {
        route
            .legs
            .first()
            .and_then(|leg| leg.duration.as_ref().map(|d| d.text.clone()))
    };
    Ok(Route {
        points,
        distance_text,
        duration_text,
    })
}

fn format_duration(seconds: u64) -> String {
    let mins = seconds.div_ceil(60);
    if mins < 90 {
        format!("{mins} min")
    } else {
        let hours = mins / 60;
        let rem = mins % 60;
        if rem == 0 {
            format!("{hours} hr")
        } else {
            format!("{hours} hr {rem} min")
        }
    }
}

/// True when `data` starts with a JPEG SOI marker.
pub fn looks_like_jpeg(data: &[u8]) -> bool {
    data.len() >= 2 && data[0] == 0xFF && data[1] == 0xD8
}

/// Read width and height from a JPEG SOF marker.
pub fn jpeg_dimensions(data: &[u8]) -> Result<(u32, u32), Error> {
    if !looks_like_jpeg(data) {
        return Err(Error::Pdf("background is not a JPEG".into()));
    }
    let mut i = 2usize;
    while i + 1 < data.len() {
        if data[i] != 0xFF {
            i += 1;
            continue;
        }
        let marker = data[i + 1];
        i += 2;
        if marker == 0xD8 || marker == 0xD9 || marker == 0x01 || (0xD0..=0xD7).contains(&marker) {
            continue;
        }
        if marker == 0xDA {
            break;
        }
        if i + 1 >= data.len() {
            break;
        }
        let seglen = u16::from_be_bytes([data[i], data[i + 1]]) as usize;
        if seglen < 2 || i + seglen > data.len() {
            break;
        }
        if (0xC0..=0xC3).contains(&marker) && seglen >= 7 {
            let height = u16::from_be_bytes([data[i + 3], data[i + 4]]) as u32;
            let width = u16::from_be_bytes([data[i + 5], data[i + 6]]) as u32;
            if width > 0 && height > 0 {
                return Ok((width, height));
            }
        }
        i += seglen;
    }
    Err(Error::Pdf("JPEG has no size markers".into()))
}

/// Accept a Maps Static body only if it is a JPEG. Google returns JSON (often
/// with HTTP 200) when the key cannot serve the image.
pub fn jpeg_from_static_map(body: &[u8]) -> Result<&[u8], Error> {
    if looks_like_jpeg(body) {
        return Ok(body);
    }
    if let Some(msg) = static_map_error(body) {
        return Err(Error::Maps(msg));
    }
    Err(Error::Maps("staticmap: response was not a JPEG".into()))
}

/// Build a spec from Google API payloads. `jpeg` must be a JPEG (use
/// [`jpeg_from_static_map`] to turn a Static Maps body into one).
pub fn spec_from_google(
    from: Address,
    to: Address,
    geocode_from: &[u8],
    geocode_to: &[u8],
    directions: &[u8],
    jpeg: &[u8],
) -> Result<EnvelopeSpec, Error> {
    // Geocode bodies are fetched so a bad address fails before directions;
    // the polyline already contains start/end, so the parsed points are unused.
    let _ = parse_geocode(geocode_from)?;
    let _ = parse_geocode(geocode_to)?;
    let route = parse_directions(directions)?;
    let jpeg = jpeg_from_static_map(jpeg)?;
    Ok(EnvelopeSpec {
        from,
        to,
        route: Some(route),
        map_jpeg: Some(jpeg.to_vec()),
    })
}

/// Surface a Google JSON error body (Static Maps returns JSON on failure).
pub fn static_map_error(body: &[u8]) -> Option<String> {
    let parsed: StatusBody = serde_json::from_slice(body).ok()?;
    if parsed.status.is_empty() || parsed.status == "OK" {
        return None;
    }
    Some(
        maps_status_error("staticmap", &parsed.status, parsed.error_message.as_deref()).to_string(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    const GEOCODE: &[u8] = br#"{
        "status": "OK",
        "results": [{"geometry": {"location": {"lat": 37.422, "lng": -122.084}}}]
    }"#;

    const DIRECTIONS: &[u8] = br#"{
        "status": "OK",
        "routes": [{
            "overview_polyline": {"points": "_p~iF~ps|U_ulLnnqC_mqNvxq`@"},
            "legs": [{
                "distance": {"text": "5.9 km", "value": 5900},
                "duration": {"text": "11 mins", "value": 658}
            }]
        }]
    }"#;

    #[test]
    fn key_placeholders_are_unusable() {
        assert!(!api_key_usable(None));
        assert!(!api_key_usable(Some("")));
        assert!(!api_key_usable(Some("  stub  ")));
        assert!(!api_key_usable(Some("REPLACE_WITH_GOOGLE_MAPS_API_KEY")));
        assert!(api_key_usable(Some("AIzaSyDummyKeyForTests")));
    }

    #[test]
    fn geocode_url_includes_address_and_key() {
        let u = geocode_url("Mountain View, CA", "secret-key");
        assert!(u.contains("maps.googleapis.com/maps/api/geocode/json"));
        assert!(u.contains("secret-key"));
        assert!(u.contains("Mountain"));
    }

    #[test]
    fn parse_geocode_ok() {
        let ll = parse_geocode(GEOCODE).unwrap();
        assert!((ll.lat - 37.422).abs() < 1e-6);
        assert!((ll.lng + 122.084).abs() < 1e-6);
    }

    #[test]
    fn parse_geocode_denied() {
        let err =
            parse_geocode(br#"{"status":"REQUEST_DENIED","error_message":"bad key"}"#).unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("REQUEST_DENIED"));
        assert!(msg.contains("bad key"));
    }

    #[test]
    fn parse_directions_ok() {
        let route = parse_directions(DIRECTIONS).unwrap();
        assert!(route.points.len() >= 2);
        assert_eq!(route.distance_text.as_deref(), Some("3.7 miles"));
        assert_eq!(route.duration_text.as_deref(), Some("11 min"));
    }

    #[test]
    fn jpeg_sof_size() {
        // SOI + SOF0 with segment length 11 (1 component): height 283, width 640.
        let mut jpeg = vec![0xFF, 0xD8, 0xFF, 0xC0, 0x00, 0x0B, 0x08];
        jpeg.extend_from_slice(&283u16.to_be_bytes());
        jpeg.extend_from_slice(&640u16.to_be_bytes());
        jpeg.extend_from_slice(&[1, 1, 0x11, 0x00]);
        assert_eq!(jpeg_dimensions(&jpeg).unwrap(), (640, 283));
    }

    #[test]
    fn spec_from_google_embeds_jpeg() {
        let from = Address::parse("Mountain View, CA").unwrap();
        let to = Address::parse("San Francisco, CA").unwrap();
        let mut jpeg = vec![0xFF, 0xD8, 0xFF, 0xC0, 0x00, 0x0B, 0x08];
        jpeg.extend_from_slice(&283u16.to_be_bytes());
        jpeg.extend_from_slice(&640u16.to_be_bytes());
        jpeg.extend_from_slice(&[1, 1, 0x11, 0x00]);
        let spec = spec_from_google(from, to, GEOCODE, GEOCODE, DIRECTIONS, &jpeg).unwrap();
        assert!(spec.map_jpeg.is_some());
        assert_eq!(spec.route.as_ref().unwrap().points.len(), 3);
    }

    #[test]
    fn spec_from_google_requires_jpeg() {
        let from = Address::parse("Mountain View, CA").unwrap();
        let to = Address::parse("San Francisco, CA").unwrap();
        let err =
            spec_from_google(from, to, GEOCODE, GEOCODE, DIRECTIONS, b"not a jpeg").unwrap_err();
        assert!(err.to_string().contains("not a JPEG"));
    }

    #[test]
    fn jpeg_from_static_map_surfaces_json_error() {
        let err = jpeg_from_static_map(
            br#"{"status":"REQUEST_DENIED","error_message":"Static Maps disabled"}"#,
        )
        .unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("REQUEST_DENIED"));
        assert!(msg.contains("Static Maps disabled"));
    }
}
