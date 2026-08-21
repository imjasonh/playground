//! Draw a US #10 envelope PDF.

use pdf_writer::types::{LineCapStyle, LineJoinStyle};
use pdf_writer::{Content, Filter, Name, Pdf, Rect, Ref, Str, TextStr};

use crate::address::Address;
use crate::error::Error;
use crate::geo::{format_miles, Bounds};
use crate::maps::{jpeg_dimensions, EnvelopeSpec, MapSource};

/// US #10 business envelope, in PDF points (1/72 inch).
pub const PAGE_W: f32 = 9.5 * 72.0;
pub const PAGE_H: f32 = 4.125 * 72.0;

const FONT_R: Name = Name(b"R");
const FONT_B: Name = Name(b"B");
const IMG: Name = Name(b"Im");
const GS: Name = Name(b"GS");

const LAND: (f32, f32, f32) = (0.957, 0.941, 0.910);
const WATER: (f32, f32, f32) = (0.655, 0.816, 0.922);
const PARK: (f32, f32, f32) = (0.769, 0.886, 0.718);
const ROAD: (f32, f32, f32) = (0.98, 0.98, 0.97);
const ROAD_EDGE: (f32, f32, f32) = (0.82, 0.80, 0.76);
const HIGHWAY: (f32, f32, f32) = (0.976, 0.839, 0.361);
const ROUTE: (f32, f32, f32) = (0.102, 0.451, 0.910);
const INK: (f32, f32, f32) = (0.12, 0.12, 0.14);
const MUTED: (f32, f32, f32) = (0.35, 0.37, 0.40);
const CARD: (f32, f32, f32) = (1.0, 0.99, 0.97);
const STAMP: (f32, f32, f32) = (0.55, 0.22, 0.22);
const PIN_FROM: (f32, f32, f32) = (0.204, 0.659, 0.325);
const PIN_TO: (f32, f32, f32) = (0.918, 0.263, 0.208);

/// Write one #10 envelope as a PDF.
pub fn render(spec: &EnvelopeSpec) -> Result<Vec<u8>, Error> {
    let mut pdf = Pdf::new();
    let catalog_id = Ref::new(1);
    let pages_id = Ref::new(2);
    let page_id = Ref::new(3);
    let content_id = Ref::new(4);
    let font_r_id = Ref::new(5);
    let font_b_id = Ref::new(6);
    let gs_id = Ref::new(7);
    let info_id = Ref::new(8);
    let image_id = Ref::new(9);

    let jpeg = spec
        .map_jpeg
        .as_deref()
        .filter(|bytes| jpeg_dimensions(bytes).is_ok());
    let jpeg_size = match jpeg {
        Some(bytes) => Some(jpeg_dimensions(bytes)?),
        None => None,
    };

    pdf.catalog(catalog_id).pages(pages_id);
    pdf.pages(pages_id).kids([page_id]).count(1);

    {
        let mut page = pdf.page(page_id);
        page.media_box(Rect::new(0.0, 0.0, PAGE_W, PAGE_H));
        page.parent(pages_id);
        page.contents(content_id);
        let mut resources = page.resources();
        {
            let mut fonts = resources.fonts();
            fonts.pair(FONT_R, font_r_id);
            fonts.pair(FONT_B, font_b_id);
        }
        resources.ext_g_states().pair(GS, gs_id);
        if jpeg_size.is_some() {
            resources.x_objects().pair(IMG, image_id);
        }
    }

    pdf.type1_font(font_r_id)
        .base_font(Name(b"Helvetica"))
        .encoding_predefined(Name(b"WinAnsiEncoding"));
    pdf.type1_font(font_b_id)
        .base_font(Name(b"Helvetica-Bold"))
        .encoding_predefined(Name(b"WinAnsiEncoding"));
    pdf.ext_graphics(gs_id)
        .non_stroking_alpha(0.90)
        .stroking_alpha(0.90);

    pdf.document_info(info_id)
        .title(TextStr("Mapvelope"))
        .creator(TextStr("mapvelopes"));

    if let (Some(bytes), Some((w, h))) = (jpeg, jpeg_size) {
        let mut image = pdf.image_xobject(image_id, bytes);
        image.filter(Filter::DctDecode);
        image.width(w as i32);
        image.height(h as i32);
        image.color_space().device_rgb();
        image.bits_per_component(8);
    }

    let mut content = Content::new();
    if jpeg_size.is_some() {
        paint_jpeg(&mut content);
    } else {
        paint_schematic(&mut content, spec);
    }
    paint_overlays(&mut content, spec, jpeg_size.is_some());
    pdf.stream(content_id, &content.finish());
    Ok(pdf.finish())
}

fn paint_jpeg(content: &mut Content) {
    content.save_state();
    content.transform([PAGE_W, 0.0, 0.0, PAGE_H, 0.0, 0.0]);
    content.x_object(IMG);
    content.restore_state();
}

fn paint_schematic(content: &mut Content, spec: &EnvelopeSpec) {
    fill_rgb(content, LAND);
    content.rect(0.0, 0.0, PAGE_W, PAGE_H);
    content.fill_nonzero();

    content.save_state();
    content.rect(0.0, 0.0, PAGE_W, PAGE_H);
    content.clip_nonzero();
    content.end_path();

    let mut rng = crate::geo::map_rng(&spec.from, &spec.to);
    draw_water(content, &mut rng);
    draw_parks(content, &mut rng);
    draw_streets(content, &mut rng);

    let bounds = Bounds::for_points(&spec.route.points);
    draw_route(content, spec, bounds);

    content.restore_state();
}

fn draw_water(content: &mut Content, rng: &mut impl crate::geo::RngF32) {
    fill_rgb(content, WATER);
    let blobs = 2 + (rng.range(0.0, 1.5) as i32);
    for _ in 0..blobs {
        let cx = rng.range(-40.0, PAGE_W + 40.0);
        let cy = rng.range(-20.0, PAGE_H + 20.0);
        let rx = rng.range(50.0, 140.0);
        let ry = rng.range(24.0, 70.0);
        ellipse(content, cx, cy, rx, ry);
        content.fill_nonzero();
    }
}

fn draw_parks(content: &mut Content, rng: &mut impl crate::geo::RngF32) {
    fill_rgb(content, PARK);
    let n = 3 + (rng.range(0.0, 3.0) as i32);
    for _ in 0..n {
        let x = rng.range(10.0, PAGE_W - 80.0);
        let y = rng.range(10.0, PAGE_H - 50.0);
        let w = rng.range(28.0, 90.0);
        let h = rng.range(18.0, 48.0);
        rounded_rect(content, x, y, w, h, 4.0);
        content.fill_nonzero();
    }
}

fn draw_streets(content: &mut Content, rng: &mut impl crate::geo::RngF32) {
    let angle = rng.range(-0.18, 0.18);
    let (sin, cos) = angle.sin_cos();
    let spacing_x = rng.range(16.0, 22.0);
    let spacing_y = rng.range(14.0, 19.0);

    content.save_state();
    // Rotate about the page center so the grid is not perfectly axis-aligned.
    let cx = PAGE_W / 2.0;
    let cy = PAGE_H / 2.0;
    content.transform([
        cos,
        sin,
        -sin,
        cos,
        cx - cos * cx + sin * cy,
        cy - sin * cx - cos * cy,
    ]);

    let span = PAGE_W.max(PAGE_H) + 80.0;
    let mut i = 0;
    let mut x = -span;
    while x < span {
        let highway = i % 7 == 0;
        if highway {
            stroke_rgb(content, ROAD_EDGE);
            content.set_line_width(3.2);
            content.set_line_cap(LineCapStyle::ButtCap);
            content.move_to(x, -span);
            content.line_to(x, span);
            content.stroke();
            stroke_rgb(content, HIGHWAY);
            content.set_line_width(2.0);
            content.move_to(x, -span);
            content.line_to(x, span);
            content.stroke();
        } else {
            stroke_rgb(content, ROAD_EDGE);
            content.set_line_width(1.15);
            content.move_to(x, -span);
            content.line_to(x, span);
            content.stroke();
            stroke_rgb(content, ROAD);
            content.set_line_width(0.75);
            content.move_to(x, -span);
            content.line_to(x, span);
            content.stroke();
        }
        x += spacing_x;
        i += 1;
    }

    i = 0;
    let mut y = -span;
    while y < span {
        let highway = i % 8 == 0;
        if highway {
            stroke_rgb(content, ROAD_EDGE);
            content.set_line_width(2.6);
            content.move_to(-span, y);
            content.line_to(span, y);
            content.stroke();
            stroke_rgb(content, HIGHWAY);
            content.set_line_width(1.6);
            content.move_to(-span, y);
            content.line_to(span, y);
            content.stroke();
        } else {
            stroke_rgb(content, ROAD_EDGE);
            content.set_line_width(1.0);
            content.move_to(-span, y);
            content.line_to(span, y);
            content.stroke();
            stroke_rgb(content, ROAD);
            content.set_line_width(0.65);
            content.move_to(-span, y);
            content.line_to(span, y);
            content.stroke();
        }
        y += spacing_y;
        i += 1;
    }
    content.restore_state();
}

fn draw_route(content: &mut Content, spec: &EnvelopeSpec, bounds: Bounds) {
    let pts: Vec<(f32, f32)> = spec
        .route
        .points
        .iter()
        .map(|p| bounds.project(*p, PAGE_W, PAGE_H))
        .collect();
    if pts.len() < 2 {
        return;
    }

    content.set_line_cap(LineCapStyle::RoundCap);
    content.set_line_join(LineJoinStyle::RoundJoin);

    stroke_rgb(content, (1.0, 1.0, 1.0));
    content.set_line_width(7.0);
    polyline(content, &pts);
    content.stroke();

    stroke_rgb(content, ROUTE);
    content.set_line_width(3.4);
    polyline(content, &pts);
    content.stroke();

    if let (Some(start), Some(end)) = (pts.first(), pts.last()) {
        pin(content, start.0, start.1, PIN_FROM);
        pin(content, end.0, end.1, PIN_TO);
    }
}

fn polyline(content: &mut Content, pts: &[(f32, f32)]) {
    let mut iter = pts.iter();
    if let Some((x, y)) = iter.next() {
        content.move_to(*x, *y);
        for (x, y) in iter {
            content.line_to(*x, *y);
        }
    }
}

fn pin(content: &mut Content, x: f32, y: f32, color: (f32, f32, f32)) {
    let h = 16.0;
    let r = 5.2;
    fill_rgb(content, color);
    content.move_to(x, y);
    content.cubic_to(x - r * 1.4, y + h * 0.45, x - r, y + h - r, x, y + h - 0.2);
    content.cubic_to(x + r, y + h - r, x + r * 1.4, y + h * 0.45, x, y);
    content.close_path();
    content.fill_nonzero();
    fill_rgb(content, (1.0, 1.0, 1.0));
    ellipse(content, x, y + h - r * 0.15, 2.1, 2.1);
    content.fill_nonzero();
}

fn paint_overlays(content: &mut Content, spec: &EnvelopeSpec, has_photo: bool) {
    let return_h = card_height(&spec.from, 9.0, 11.0);
    let return_w = 210.0;
    let return_x = 16.0;
    let return_y = PAGE_H - 16.0 - return_h;

    let dest_h = card_height(&spec.to, 11.0, 13.5);
    let dest_w = 260.0;
    let dest_x = 250.0;
    let dest_y = 92.0;

    // Translucent cards so type stays readable on both schematic and photo maps.
    content.save_state();
    content.set_parameters(GS);
    fill_rgb(content, CARD);
    rounded_rect(content, return_x, return_y, return_w, return_h, 3.0);
    content.fill_nonzero();
    fill_rgb(content, CARD);
    rounded_rect(content, dest_x, dest_y, dest_w, dest_h, 3.5);
    content.fill_nonzero();
    content.restore_state();

    write_address(
        content,
        &spec.from,
        return_x + 8.0,
        return_y + return_h - 14.0,
        9.0,
        11.0,
        false,
    );
    write_address(
        content,
        &spec.to,
        dest_x + 12.0,
        dest_y + dest_h - 16.0,
        11.0,
        13.5,
        true,
    );

    draw_stamp(content);
    draw_legend(content, spec, has_photo);
}

fn card_height(addr: &Address, size: f32, leading: f32) -> f32 {
    let lines = addr.lines().len().max(1) as f32;
    12.0 + (lines - 1.0) * leading + size
}

fn write_address(
    content: &mut Content,
    addr: &Address,
    x: f32,
    top: f32,
    size: f32,
    leading: f32,
    delivery: bool,
) {
    fill_rgb(content, INK);
    for (i, line) in addr.lines().iter().enumerate() {
        let y = top - i as f32 * leading;
        let font = if delivery && i == 0 { FONT_B } else { FONT_R };
        let fitted = fit_chars(line, if delivery { 32 } else { 36 });
        show_text(content, font, size, x, y, &fitted);
    }
}

fn draw_stamp(content: &mut Content) {
    let w = 62.0;
    let h = 72.0;
    let x = PAGE_W - 16.0 - w;
    let y = PAGE_H - 16.0 - h;
    content.set_dash_pattern([2.5, 2.0], 0.0);
    stroke_rgb(content, STAMP);
    content.set_line_width(0.9);
    rounded_rect(content, x, y, w, h, 2.0);
    content.stroke();
    content.set_dash_pattern([], 0.0);
    fill_rgb(content, STAMP);
    show_text(content, FONT_R, 6.0, x + 7.0, y + h / 2.0 + 4.0, "PLACE");
    show_text(content, FONT_R, 6.0, x + 7.0, y + h / 2.0 - 5.0, "STAMP");
    show_text(content, FONT_R, 6.0, x + 7.0, y + h / 2.0 - 14.0, "HERE");
}

fn draw_legend(content: &mut Content, spec: &EnvelopeSpec, has_photo: bool) {
    fill_rgb(content, MUTED);
    let distance = spec
        .route
        .distance_text
        .clone()
        .unwrap_or_else(|| format_miles(spec.route.path_miles()));
    let mut legend = distance;
    if let Some(dur) = &spec.route.duration_text {
        legend = format!("{legend}  ·  {dur}");
    }
    show_text(content, FONT_R, 7.0, 16.0, 18.0, &legend);

    let attrib = match spec.source {
        MapSource::Google if has_photo => "Map data © Google",
        MapSource::Google => "Route data © Google",
        MapSource::Schematic => "Schematic route, not a surveyed map",
    };
    show_text(content, FONT_R, 6.5, 16.0, 8.0, attrib);
}

fn show_text(content: &mut Content, font: Name, size: f32, x: f32, y: f32, text: &str) {
    content.begin_text();
    content.set_font(font, size);
    content.next_line(x, y);
    content.show(Str(&winansi(text)));
    content.end_text();
}

fn fill_rgb(content: &mut Content, c: (f32, f32, f32)) {
    content.set_fill_rgb(c.0, c.1, c.2);
}

fn stroke_rgb(content: &mut Content, c: (f32, f32, f32)) {
    content.set_stroke_rgb(c.0, c.1, c.2);
}

fn ellipse(content: &mut Content, cx: f32, cy: f32, rx: f32, ry: f32) {
    let k = 0.552_284_8;
    let kx = k * rx;
    let ky = k * ry;
    content.move_to(cx + rx, cy);
    content.cubic_to(cx + rx, cy + ky, cx + kx, cy + ry, cx, cy + ry);
    content.cubic_to(cx - kx, cy + ry, cx - rx, cy + ky, cx - rx, cy);
    content.cubic_to(cx - rx, cy - ky, cx - kx, cy - ry, cx, cy - ry);
    content.cubic_to(cx + kx, cy - ry, cx + rx, cy - ky, cx + rx, cy);
    content.close_path();
}

fn rounded_rect(content: &mut Content, x: f32, y: f32, w: f32, h: f32, r: f32) {
    let r = r.min(w / 2.0).min(h / 2.0);
    let k = 0.552_284_8 * r;
    content.move_to(x + r, y);
    content.line_to(x + w - r, y);
    content.cubic_to(x + w - r + k, y, x + w, y + r - k, x + w, y + r);
    content.line_to(x + w, y + h - r);
    content.cubic_to(x + w, y + h - r + k, x + w - r + k, y + h, x + w - r, y + h);
    content.line_to(x + r, y + h);
    content.cubic_to(x + r - k, y + h, x, y + h - r + k, x, y + h - r);
    content.line_to(x, y + r);
    content.cubic_to(x, y + r - k, x + r - k, y, x + r, y);
    content.close_path();
}

fn fit_chars(s: &str, max: usize) -> String {
    let n = s.chars().count();
    if n <= max {
        s.to_string()
    } else {
        let mut out: String = s.chars().take(max.saturating_sub(3)).collect();
        out.push_str("...");
        out
    }
}

fn winansi(s: &str) -> Vec<u8> {
    s.chars()
        .map(|c| {
            let u = c as u32;
            if u == 0x20AC {
                0x80
            } else if u < 0x80 || (0xA0..=0xFF).contains(&u) {
                u as u8
            } else {
                b'?'
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::address::Address;
    use crate::maps::EnvelopeSpec;

    fn pdf_for(from: &str, to: &str) -> Vec<u8> {
        let spec =
            EnvelopeSpec::schematic(Address::parse(from).unwrap(), Address::parse(to).unwrap());
        render(&spec).unwrap()
    }

    #[test]
    fn schematic_pdf_is_validish() {
        let pdf = pdf_for(
            "Ada Example\n1600 Amphitheatre Parkway\nMountain View, CA 94043",
            "Bob Example\n350 Fifth Avenue\nNew York, NY 10118",
        );
        assert!(pdf.starts_with(b"%PDF-"));
        assert!(pdf.windows(5).any(|w| w == b"%%EOF"));
        assert!(pdf.windows(9).any(|w| w == b"Helvetica"));
        // Content streams store address text as PDF literal strings.
        assert!(pdf.windows(11).any(|w| w == b"Ada Example"));
        assert!(pdf.windows(11).any(|w| w == b"Bob Example"));
        assert!(pdf.len() > 2_000);
        assert_eq!((PAGE_W / 72.0 * 10.0).round() / 10.0, 9.5);
        assert_eq!((PAGE_H / 72.0 * 1000.0).round() / 1000.0, 4.125);
    }

    #[test]
    fn different_routes_differ() {
        let a = pdf_for("Mountain View, CA", "New York, NY");
        let b = pdf_for("Seattle, WA", "Miami, FL");
        assert_ne!(a, b);
    }

    #[test]
    fn same_addresses_are_stable() {
        let a = pdf_for("Mountain View, CA", "New York, NY");
        let b = pdf_for("Mountain View, CA", "New York, NY");
        assert_eq!(a, b);
    }
}
