//! Google Maps URL builders, JSON parsers, and envelope-spec assembly.

use serde::Deserialize;
use url::Url;

use crate::address::Address;
use crate::error::Error;
use crate::geo::{decode_polyline, encode_polyline, format_miles, subsample, LatLng, Route};

/// Static Maps look. The PDF still washes the JPEG toward cream so
/// address type stays readable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MapStyle {
    /// Default Google roadmap. Blue route, green/red pins.
    Google,
    /// Cream land, muted water, no POIs. Brown route.
    Paper,
    /// Google terrain shading.
    Terrain,
    /// Desaturated roadmap. Dark gray route.
    Muted,
    /// Satellite plus labels. Hybrid needs a heavier PDF wash.
    Hybrid,
}

impl MapStyle {
    /// Parse a form, query, or JSON value. Missing or empty is Google.
    pub fn parse(raw: Option<&str>) -> Result<Self, Error> {
        match raw.map(str::trim).filter(|s| !s.is_empty()) {
            None => Ok(Self::Google),
            Some(s) if s.eq_ignore_ascii_case("google") => Ok(Self::Google),
            Some(s) if s.eq_ignore_ascii_case("paper") => Ok(Self::Paper),
            Some(s) if s.eq_ignore_ascii_case("terrain") => Ok(Self::Terrain),
            Some(s) if s.eq_ignore_ascii_case("muted") => Ok(Self::Muted),
            Some(s) if s.eq_ignore_ascii_case("hybrid") => Ok(Self::Hybrid),
            Some(s) => Err(Error::BadRequest(format!(
                "unknown style {s:?}; use google, paper, terrain, muted, or hybrid"
            ))),
        }
    }

    /// JPEG opacity over the cream page fill. Hybrid is busier, so it
    /// gets more wash.
    pub fn map_alpha(self) -> f32 {
        match self {
            Self::Hybrid => 0.4,
            _ => 0.68,
        }
    }
}

/// US envelope stock. Default is #10 (business).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EnvelopeSize {
    /// 9.5 × 4.125 in. Common business envelope.
    Ten,
    /// 8.875 × 3.875 in. Fits inside a #10.
    Nine,
    /// 7.5 × 3.875 in.
    Monarch,
    /// 6.5 × 3.625 in. Also written #6¾.
    SixThreeQuarter,
    /// 7.25 × 5.25 in. Invitation / A7.
    A7,
}

impl EnvelopeSize {
    /// Every stock the form and CLI offer.
    pub const ALL: [Self; 5] = [
        Self::Ten,
        Self::Nine,
        Self::Monarch,
        Self::SixThreeQuarter,
        Self::A7,
    ];

    /// Parse a form, query, JSON, or CLI value. Missing or empty is #10.
    pub fn parse(raw: Option<&str>) -> Result<Self, Error> {
        match raw.map(str::trim).filter(|s| !s.is_empty()) {
            None => Ok(Self::Ten),
            Some(s) => match canonical_size(s).as_str() {
                "10" | "ten" | "business" => Ok(Self::Ten),
                "9" | "nine" => Ok(Self::Nine),
                "monarch" | "7.5" | "7-1/2" => Ok(Self::Monarch),
                "6-3/4" | "6.75" | "6-75" | "63/4" | "6-3-4" => Ok(Self::SixThreeQuarter),
                "a7" | "invitation" => Ok(Self::A7),
                _ => Err(Error::BadRequest(format!(
                    "unknown size {s:?}; use 10, 9, monarch, 6-3/4, or a7"
                ))),
            },
        }
    }

    /// Form / query id (`10`, `9`, `monarch`, `6-3/4`, `a7`).
    pub fn id(self) -> &'static str {
        match self {
            Self::Ten => "10",
            Self::Nine => "9",
            Self::Monarch => "monarch",
            Self::SixThreeQuarter => "6-3/4",
            Self::A7 => "a7",
        }
    }

    /// Width × height in inches, flap along the long edge.
    pub fn inches(self) -> (f32, f32) {
        match self {
            Self::Ten => (9.5, 4.125),
            Self::Nine => (8.875, 3.875),
            Self::Monarch => (7.5, 3.875),
            Self::SixThreeQuarter => (6.5, 3.625),
            Self::A7 => (7.25, 5.25),
        }
    }

    /// Width × height in PDF points (1/72 inch).
    pub fn points(self) -> (f32, f32) {
        let (w, h) = self.inches();
        (w * 72.0, h * 72.0)
    }

    /// Static Maps `size=` before `scale=2`. Longest side is 640.
    pub fn static_map_pixels(self) -> (u32, u32) {
        let (w, h) = self.inches();
        const MAX: f32 = 640.0;
        if w >= h {
            let ph = ((MAX * h / w).round() as u32).clamp(1, 640);
            (640, ph)
        } else {
            let pw = ((MAX * w / h).round() as u32).clamp(1, 640);
            (pw, 640)
        }
    }
}

fn canonical_size(s: &str) -> String {
    let mut t = s.trim().to_ascii_lowercase();
    t = t.replace('¾', "3/4");
    t.retain(|c| !c.is_whitespace() && c != '_');
    let t = t.trim_start_matches('#');
    let t = t.strip_prefix("number").unwrap_or(t);
    let t = t.strip_prefix("no.").unwrap_or(t);
    let t = t.strip_prefix("no").unwrap_or(t);
    t.trim_start_matches(['#', '-', '.']).to_string()
}

/// Everything [`crate::render::render`] needs to draw one envelope.
#[derive(Debug, Clone)]
pub struct EnvelopeSpec {
    pub from: Address,
    pub to: Address,
    pub route: Option<Route>,
    pub map_jpeg: Option<Vec<u8>>,
    pub map_style: MapStyle,
    pub size: EnvelopeSize,
}

impl EnvelopeSpec {
    /// Addresses only. No Maps calls, no background image.
    pub fn no_map(from: Address, to: Address) -> Self {
        EnvelopeSpec {
            from,
            to,
            route: None,
            map_jpeg: None,
            map_style: MapStyle::Google,
            size: EnvelopeSize::Ten,
        }
    }
}

/// True when `key` is sent to Google. Empty strings and the
/// `REPLACE_…` / `stub` placeholders are treated as unset.
pub fn api_key_usable(key: Option<&str>) -> bool {
    match key.map(str::trim) {
        None | Some("") => false,
        Some("stub") | Some("STUB") => false,
        Some(k) if k.starts_with("REPLACE_") => false,
        Some(_) => true,
    }
}

/// A geocoded point plus envelope print lines.
#[derive(Debug, Clone)]
pub struct Geocode {
    pub location: LatLng,
    pub postal_lines: Vec<String>,
}

/// One Places Autocomplete prediction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PlaceSuggestion {
    pub label: String,
    pub place_id: String,
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

/// Places Autocomplete JSON API for the form typeahead.
pub fn places_autocomplete_url(input: &str, key: &str) -> String {
    let mut url = Url::parse("https://maps.googleapis.com/maps/api/place/autocomplete/json")
        .expect("static places autocomplete URL");
    url.query_pairs_mut()
        .append_pair("input", input)
        .append_pair("types", "address")
        .append_pair("key", key);
    url.to_string()
}

/// Place Details JSON API for a prediction's `place_id`.
pub fn place_details_url(place_id: &str, key: &str) -> String {
    let mut url = Url::parse("https://maps.googleapis.com/maps/api/place/details/json")
        .expect("static place details URL");
    url.query_pairs_mut()
        .append_pair("place_id", place_id)
        .append_pair("fields", "address_component,formatted_address")
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

const PAPER_STYLES: &[&str] = &[
    "saturation:-20|lightness:8",
    "feature:poi|visibility:off",
    "feature:transit|visibility:off",
    "feature:landscape|element:geometry|color:0xF4ECD8",
    "feature:water|element:geometry|color:0xC5D4CE",
    "feature:poi.park|element:geometry|color:0xD5E0C8",
    "feature:road|element:geometry.fill|color:0xE8DCC4",
    "feature:road|element:geometry.stroke|color:0xD4C4A8",
    "feature:road.highway|element:geometry.fill|color:0xCBB892",
    "feature:road|element:labels.icon|visibility:off",
    "element:labels.text.fill|color:0x5C5346",
    "element:labels.text.stroke|color:0xF4ECD8",
];

const TERRAIN_STYLES: &[&str] = &[
    "feature:poi|visibility:off",
    "feature:transit|visibility:off",
];

const MUTED_STYLES: &[&str] = &[
    "saturation:-85|lightness:12",
    "feature:poi|visibility:off",
    "feature:transit|visibility:off",
    "feature:road|element:labels.icon|visibility:off",
];

/// Static Maps request: route polyline plus start/end markers. JPEG, envelope aspect.
pub fn static_map_url(route: &Route, key: &str, style: MapStyle, size: EnvelopeSize) -> String {
    let mut url =
        Url::parse("https://maps.googleapis.com/maps/api/staticmap").expect("static map URL");
    let pts = subsample(&route.points, 80);
    let enc = encode_polyline(&pts);
    let (maptype, path_color, start_marker, end_marker, extra_styles) = match style {
        MapStyle::Paper => (
            "roadmap",
            "0x5C3A21ff",
            "color:0x5C3A21|size:mid",
            "color:0x8B1E1E|size:mid",
            PAPER_STYLES,
        ),
        MapStyle::Terrain => (
            "terrain",
            "0x1A73E8ff",
            "color:0x34A853|size:mid",
            "color:0xEA4335|size:mid",
            TERRAIN_STYLES,
        ),
        MapStyle::Muted => (
            "roadmap",
            "0x333333ff",
            "color:0x555555|size:mid",
            "color:0x111111|size:mid",
            MUTED_STYLES,
        ),
        MapStyle::Hybrid => (
            "hybrid",
            "0xF9E27Aff",
            "color:yellow|size:mid",
            "color:red|size:mid",
            &[] as &[&str],
        ),
        MapStyle::Google => (
            "roadmap",
            "0x1A73E8ff",
            "color:0x34A853|size:mid",
            "color:0xEA4335|size:mid",
            &[] as &[&str],
        ),
    };
    let path = format!("weight:5|color:{path_color}|enc:{enc}");
    {
        let mut q = url.query_pairs_mut();
        let (pw, ph) = size.static_map_pixels();
        q.append_pair("size", &format!("{pw}x{ph}"));
        q.append_pair("scale", "2");
        q.append_pair("maptype", maptype);
        q.append_pair("format", "jpg");
        q.append_pair("path", &path);
        if let Some(start) = route.start() {
            q.append_pair("markers", &format!("{start_marker}|{}", format_ll(start)));
        }
        if let Some(end) = route.end() {
            q.append_pair("markers", &format!("{end_marker}|{}", format_ll(end)));
        }
        for s in extra_styles {
            q.append_pair("style", s);
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
    #[serde(default)]
    formatted_address: Option<String>,
    #[serde(default)]
    address_components: Vec<AddressComponent>,
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
struct AddressComponent {
    long_name: String,
    short_name: String,
    #[serde(default)]
    types: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct AutocompleteBody {
    status: String,
    #[serde(default)]
    error_message: Option<String>,
    #[serde(default)]
    predictions: Vec<AutocompletePrediction>,
}

#[derive(Debug, Deserialize)]
struct AutocompletePrediction {
    description: String,
    place_id: String,
}

#[derive(Debug, Deserialize)]
struct PlaceDetailsBody {
    status: String,
    #[serde(default)]
    error_message: Option<String>,
    #[serde(default)]
    result: Option<PlaceDetailsResult>,
}

#[derive(Debug, Deserialize)]
struct PlaceDetailsResult {
    #[serde(default)]
    formatted_address: Option<String>,
    #[serde(default)]
    address_components: Vec<AddressComponent>,
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

/// Parse a Geocoding API body. Location plus envelope lines from components.
pub fn parse_geocode(body: &[u8]) -> Result<Geocode, Error> {
    let parsed: GeocodeBody =
        serde_json::from_slice(body).map_err(|e| Error::Maps(format!("geocode JSON: {e}")))?;
    if parsed.status != "OK" {
        return Err(maps_status_error(
            "geocode",
            &parsed.status,
            parsed.error_message.as_deref(),
        ));
    }
    let result = parsed
        .results
        .first()
        .ok_or_else(|| Error::Maps("geocode: OK but no results".into()))?;
    let loc = &result.geometry.location;
    Ok(Geocode {
        location: LatLng::new(loc.lat, loc.lng),
        postal_lines: postal_lines(
            &result.address_components,
            result.formatted_address.as_deref(),
        ),
    })
}

/// Parse Places Autocomplete. `ZERO_RESULTS` is an empty list, not an error.
pub fn parse_autocomplete(body: &[u8]) -> Result<Vec<PlaceSuggestion>, Error> {
    let parsed: AutocompleteBody =
        serde_json::from_slice(body).map_err(|e| Error::Maps(format!("places JSON: {e}")))?;
    if parsed.status == "ZERO_RESULTS" {
        return Ok(Vec::new());
    }
    if parsed.status != "OK" {
        return Err(maps_status_error(
            "places",
            &parsed.status,
            parsed.error_message.as_deref(),
        ));
    }
    Ok(parsed
        .predictions
        .into_iter()
        .map(|p| PlaceSuggestion {
            label: p.description,
            place_id: p.place_id,
        })
        .collect())
}

/// Parse Place Details into envelope print lines.
pub fn parse_place_details(body: &[u8]) -> Result<Vec<String>, Error> {
    let parsed: PlaceDetailsBody = serde_json::from_slice(body)
        .map_err(|e| Error::Maps(format!("place details JSON: {e}")))?;
    if parsed.status != "OK" {
        return Err(maps_status_error(
            "place",
            &parsed.status,
            parsed.error_message.as_deref(),
        ));
    }
    let result = parsed
        .result
        .ok_or_else(|| Error::Maps("place: OK but no result".into()))?;
    let lines = postal_lines(
        &result.address_components,
        result.formatted_address.as_deref(),
    );
    if lines.is_empty() {
        return Err(Error::Maps("place: no address lines".into()));
    }
    Ok(lines)
}

fn postal_lines(components: &[AddressComponent], formatted: Option<&str>) -> Vec<String> {
    let mut lines = Vec::new();
    if let Some(street) = street_line(components) {
        lines.push(street);
    }
    if let Some(city) = city_line(components) {
        lines.push(city);
    }
    if let Some(country) = component(components, "country") {
        let short = country.short_name.as_str();
        if short != "US" && !short.eq_ignore_ascii_case("USA") {
            lines.push(country.long_name.clone());
        }
    }
    if lines.is_empty() {
        if let Some(formatted) = formatted {
            return lines_from_formatted(formatted);
        }
    }
    lines
}

fn component<'a>(cs: &'a [AddressComponent], ty: &str) -> Option<&'a AddressComponent> {
    cs.iter().find(|c| c.types.iter().any(|t| t == ty))
}

fn street_line(cs: &[AddressComponent]) -> Option<String> {
    let num = component(cs, "street_number").map(|c| c.short_name.as_str());
    let route = component(cs, "route").map(|c| c.short_name.as_str());
    let unit = component(cs, "subpremise").map(|c| c.short_name.as_str());
    match (num, route) {
        (Some(n), Some(r)) => {
            let mut s = format!("{n} {r}");
            if let Some(u) = unit {
                if u.chars().all(|c| c.is_ascii_digit()) {
                    s.push_str(" #");
                    s.push_str(u);
                } else {
                    s.push(' ');
                    s.push_str(u);
                }
            }
            Some(s)
        }
        (None, Some(r)) => Some(r.to_string()),
        (Some(n), None) => Some(n.to_string()),
        (None, None) => component(cs, "premise").map(|c| c.long_name.clone()),
    }
}

fn city_name(cs: &[AddressComponent]) -> Option<&str> {
    component(cs, "locality")
        .or_else(|| component(cs, "postal_town"))
        .or_else(|| component(cs, "sublocality_level_1"))
        .or_else(|| component(cs, "sublocality"))
        .map(|c| c.long_name.as_str())
}

fn city_line(cs: &[AddressComponent]) -> Option<String> {
    let city = city_name(cs)?;
    let state = component(cs, "administrative_area_level_1").map(|c| c.short_name.as_str());
    let zip = component(cs, "postal_code").map(|c| c.short_name.as_str());
    Some(match (state, zip) {
        (Some(st), Some(z)) => format!("{city}, {st} {z}"),
        (Some(st), None) => format!("{city}, {st}"),
        (None, Some(z)) => format!("{city} {z}"),
        (None, None) => city.to_string(),
    })
}

fn lines_from_formatted(formatted: &str) -> Vec<String> {
    let mut parts: Vec<&str> = formatted
        .split(',')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .collect();
    if let Some(last) = parts.last() {
        if last.eq_ignore_ascii_case("USA") || last.eq_ignore_ascii_case("United States") {
            parts.pop();
        }
    }
    if parts.len() >= 3 {
        let street = parts[0].to_string();
        let city = parts[1];
        let rest = parts[2..].join(", ");
        vec![street, format!("{city}, {rest}")]
    } else {
        parts.into_iter().map(str::to_string).collect()
    }
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
#[allow(clippy::too_many_arguments)]
pub fn spec_from_google(
    from: Address,
    to: Address,
    geocode_from: &[u8],
    geocode_to: &[u8],
    directions: &[u8],
    jpeg: &[u8],
    style: MapStyle,
    size: EnvelopeSize,
) -> Result<EnvelopeSpec, Error> {
    let from_geo = parse_geocode(geocode_from)?;
    let to_geo = parse_geocode(geocode_to)?;
    let route = parse_directions(directions)?;
    let jpeg = jpeg_from_static_map(jpeg)?;
    Ok(EnvelopeSpec {
        from: from.expand_with(&from_geo.postal_lines),
        to: to.expand_with(&to_geo.postal_lines),
        route: Some(route),
        map_jpeg: Some(jpeg.to_vec()),
        map_style: style,
        size,
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
        let geo = parse_geocode(GEOCODE).unwrap();
        assert!((geo.location.lat - 37.422).abs() < 1e-6);
        assert!((geo.location.lng + 122.084).abs() < 1e-6);
        assert!(geo.postal_lines.is_empty());
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
        let spec = spec_from_google(
            from,
            to,
            GEOCODE,
            GEOCODE,
            DIRECTIONS,
            &jpeg,
            MapStyle::Google,
            EnvelopeSize::Ten,
        )
        .unwrap();
        assert_eq!(spec.size, EnvelopeSize::Ten);
        assert!(spec.map_jpeg.is_some());
        assert_eq!(spec.route.as_ref().unwrap().points.len(), 3);
    }

    const FAKE_ST: &[u8] = br#"{
        "status": "OK",
        "results": [{
            "formatted_address": "123 Fake St, Brooklyn, NY 11231, USA",
            "address_components": [
                {"long_name": "123", "short_name": "123", "types": ["street_number"]},
                {"long_name": "Fake Street", "short_name": "Fake St", "types": ["route"]},
                {"long_name": "Brooklyn", "short_name": "Brooklyn", "types": ["political", "sublocality", "sublocality_level_1"]},
                {"long_name": "New York", "short_name": "NY", "types": ["administrative_area_level_1", "political"]},
                {"long_name": "United States", "short_name": "US", "types": ["country", "political"]},
                {"long_name": "11231", "short_name": "11231", "types": ["postal_code"]},
                {"long_name": "0001", "short_name": "0001", "types": ["postal_code_suffix"]}
            ],
            "geometry": {"location": {"lat": 40.65, "lng": -74.0}}
        }]
    }"#;

    #[test]
    fn geocode_expands_sublocality_city() {
        let geo = parse_geocode(FAKE_ST).unwrap();
        assert_eq!(geo.postal_lines, ["123 Fake St", "Brooklyn, NY 11231"]);
    }

    #[test]
    fn spec_from_google_prints_expanded_address() {
        let from = Address::parse("Ada Example\n1600 Amphitheatre Parkway").unwrap();
        let to = Address::parse("123 fake st\nbrooklyn").unwrap();
        let mut jpeg = vec![0xFF, 0xD8, 0xFF, 0xC0, 0x00, 0x0B, 0x08];
        jpeg.extend_from_slice(&8u16.to_be_bytes());
        jpeg.extend_from_slice(&8u16.to_be_bytes());
        jpeg.extend_from_slice(&[1, 1, 0x11, 0x00]);
        let spec = spec_from_google(
            from,
            to,
            GEOCODE,
            FAKE_ST,
            DIRECTIONS,
            &jpeg,
            MapStyle::Google,
            EnvelopeSize::Ten,
        )
        .unwrap();
        assert_eq!(spec.to.lines(), ["123 Fake St", "Brooklyn, NY 11231"]);
        assert_eq!(spec.from.lines()[0], "Ada Example");
    }

    #[test]
    fn parse_autocomplete_predictions() {
        let body = br#"{
            "status": "OK",
            "predictions": [
                {"description": "123 Fake St, Brooklyn, NY, USA", "place_id": "ChIJ50"},
                {"description": "123 Fake St, Springfield, IL, USA", "place_id": "ChIJxx"}
            ]
        }"#;
        let got = parse_autocomplete(body).unwrap();
        assert_eq!(got.len(), 2);
        assert_eq!(got[0].label, "123 Fake St, Brooklyn, NY, USA");
        assert_eq!(got[0].place_id, "ChIJ50");
    }

    #[test]
    fn parse_autocomplete_zero_results() {
        let got = parse_autocomplete(br#"{"status":"ZERO_RESULTS","predictions":[]}"#).unwrap();
        assert!(got.is_empty());
    }

    #[test]
    fn parse_autocomplete_denied() {
        let err =
            parse_autocomplete(br#"{"status":"REQUEST_DENIED","error_message":"Places disabled"}"#)
                .unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("REQUEST_DENIED"));
        assert!(msg.contains("Places disabled"));
    }

    #[test]
    fn parse_place_details_lines() {
        let body = br#"{
            "status": "OK",
            "result": {
                "formatted_address": "123 Fake St, Brooklyn, NY 11231, USA",
                "address_components": [
                    {"long_name": "123", "short_name": "123", "types": ["street_number"]},
                    {"long_name": "Fake Street", "short_name": "Fake St", "types": ["route"]},
                    {"long_name": "Brooklyn", "short_name": "Brooklyn", "types": ["sublocality", "sublocality_level_1"]},
                    {"long_name": "New York", "short_name": "NY", "types": ["administrative_area_level_1"]},
                    {"long_name": "United States", "short_name": "US", "types": ["country"]},
                    {"long_name": "11231", "short_name": "11231", "types": ["postal_code"]}
                ]
            }
        }"#;
        let lines = parse_place_details(body).unwrap();
        assert_eq!(lines, ["123 Fake St", "Brooklyn, NY 11231"]);
    }

    #[test]
    fn places_urls_include_key() {
        let auto = places_autocomplete_url("123 Fake", "secret-key");
        assert!(auto.contains("place/autocomplete/json"));
        assert!(auto.contains("secret-key"));
        assert!(auto.contains("types=address"));
        let details = place_details_url("ChIJ50", "secret-key");
        assert!(details.contains("place/details/json"));
        assert!(details.contains("ChIJ50"));
    }

    #[test]
    fn spec_from_google_requires_jpeg() {
        let from = Address::parse("Mountain View, CA").unwrap();
        let to = Address::parse("San Francisco, CA").unwrap();
        let err = spec_from_google(
            from,
            to,
            GEOCODE,
            GEOCODE,
            DIRECTIONS,
            b"not a jpeg",
            MapStyle::Google,
            EnvelopeSize::Ten,
        )
        .unwrap_err();
        assert!(err.to_string().contains("not a JPEG"));
    }

    #[test]
    fn style_parse() {
        assert_eq!(MapStyle::parse(None).unwrap(), MapStyle::Google);
        assert_eq!(MapStyle::parse(Some("")).unwrap(), MapStyle::Google);
        assert_eq!(MapStyle::parse(Some(" paper ")).unwrap(), MapStyle::Paper);
        assert_eq!(MapStyle::parse(Some("HYBRID")).unwrap(), MapStyle::Hybrid);
        let err = MapStyle::parse(Some("oil-paint")).unwrap_err();
        assert!(err.to_string().contains("unknown style"));
    }

    #[test]
    fn static_map_url_varies_by_style() {
        let route = parse_directions(DIRECTIONS).unwrap();
        let google = static_map_url(&route, "k", MapStyle::Google, EnvelopeSize::Ten);
        assert!(google.contains("maptype=roadmap"));
        assert!(google.contains("1A73E8"));
        let paper = static_map_url(&route, "k", MapStyle::Paper, EnvelopeSize::Ten);
        assert!(paper.contains("F4ECD8"));
        assert!(paper.contains("5C3A21"));
        let hybrid = static_map_url(&route, "k", MapStyle::Hybrid, EnvelopeSize::Ten);
        assert!(hybrid.contains("maptype=hybrid"));
        assert!(hybrid.contains("F9E27A"));
        assert!(!hybrid.contains("F4ECD8"));
        let terrain = static_map_url(&route, "k", MapStyle::Terrain, EnvelopeSize::Ten);
        assert!(terrain.contains("maptype=terrain"));
        let muted = static_map_url(&route, "k", MapStyle::Muted, EnvelopeSize::Ten);
        assert!(muted.contains("saturation"));
    }

    #[test]
    fn size_parse() {
        assert_eq!(EnvelopeSize::parse(None).unwrap(), EnvelopeSize::Ten);
        assert_eq!(EnvelopeSize::parse(Some("")).unwrap(), EnvelopeSize::Ten);
        assert_eq!(
            EnvelopeSize::parse(Some(" #10 ")).unwrap(),
            EnvelopeSize::Ten
        );
        assert_eq!(EnvelopeSize::parse(Some("ten")).unwrap(), EnvelopeSize::Ten);
        assert_eq!(
            EnvelopeSize::parse(Some("no. 10")).unwrap(),
            EnvelopeSize::Ten
        );
        assert_eq!(EnvelopeSize::parse(Some("9")).unwrap(), EnvelopeSize::Nine);
        assert_eq!(
            EnvelopeSize::parse(Some("monarch")).unwrap(),
            EnvelopeSize::Monarch
        );
        assert_eq!(
            EnvelopeSize::parse(Some("6-3/4")).unwrap(),
            EnvelopeSize::SixThreeQuarter
        );
        assert_eq!(
            EnvelopeSize::parse(Some("6.75")).unwrap(),
            EnvelopeSize::SixThreeQuarter
        );
        assert_eq!(
            EnvelopeSize::parse(Some("6¾")).unwrap(),
            EnvelopeSize::SixThreeQuarter
        );
        assert_eq!(EnvelopeSize::parse(Some("A7")).unwrap(), EnvelopeSize::A7);
        for size in EnvelopeSize::ALL {
            assert_eq!(EnvelopeSize::parse(Some(size.id())).unwrap(), size);
        }
        let err = EnvelopeSize::parse(Some("c5")).unwrap_err();
        assert!(err.to_string().contains("unknown size"));
    }

    #[test]
    fn static_map_url_matches_envelope_aspect() {
        let route = parse_directions(DIRECTIONS).unwrap();
        let ten = static_map_url(&route, "k", MapStyle::Google, EnvelopeSize::Ten);
        let (tw, th) = EnvelopeSize::Ten.static_map_pixels();
        assert!(ten.contains(&format!("size={tw}x{th}")));
        let a7 = static_map_url(&route, "k", MapStyle::Google, EnvelopeSize::A7);
        let (aw, ah) = EnvelopeSize::A7.static_map_pixels();
        assert!(a7.contains(&format!("size={aw}x{ah}")));
        assert_ne!((tw, th), (aw, ah));
        let small = EnvelopeSize::SixThreeQuarter.static_map_pixels();
        assert_ne!(small, (tw, th));
        assert_eq!(tw, 640);
        assert_eq!(aw, 640);
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
