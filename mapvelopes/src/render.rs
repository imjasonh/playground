//! Draw a US envelope PDF.

use pdf_writer::{Content, Filter, Name, Pdf, Rect, Ref, Str, TextStr};

use crate::address::Address;
use crate::error::Error;
use crate::maps::{jpeg_dimensions, EnvelopeSpec};

/// US #10 business envelope, in PDF points (1/72 inch). Overlay layout
/// scales from these when the spec picks a different stock.
pub const PAGE_W: f32 = 9.5 * 72.0;
pub const PAGE_H: f32 = 4.125 * 72.0;

const FONT_R: Name = Name(b"R");
const FONT_B: Name = Name(b"B");
const IMG: Name = Name(b"Im");
const GS: Name = Name(b"GS");

const LAND: (f32, f32, f32) = (0.957, 0.941, 0.910);
const INK: (f32, f32, f32) = (0.12, 0.12, 0.14);
const CARD: (f32, f32, f32) = (1.0, 0.99, 0.97);
const STAMP: (f32, f32, f32) = (0.55, 0.22, 0.22);

/// Write one envelope as a PDF. Page size comes from [`EnvelopeSpec::size`].
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

    let (page_w, page_h) = spec.size.points();
    let jpeg = spec.map_jpeg.as_deref();
    let jpeg_size = match jpeg {
        Some(bytes) => Some(jpeg_dimensions(bytes)?),
        None => None,
    };

    pdf.catalog(catalog_id).pages(pages_id);
    pdf.pages(pages_id).kids([page_id]).count(1);

    {
        let mut page = pdf.page(page_id);
        page.media_box(Rect::new(0.0, 0.0, page_w, page_h));
        page.parent(pages_id);
        page.contents(content_id);
        let mut resources = page.resources();
        {
            let mut fonts = resources.fonts();
            fonts.pair(FONT_R, font_r_id);
            fonts.pair(FONT_B, font_b_id);
        }
        if jpeg_size.is_some() {
            resources.ext_g_states().pair(GS, gs_id);
            resources.x_objects().pair(IMG, image_id);
        }
    }

    pdf.type1_font(font_r_id)
        .base_font(Name(b"Helvetica"))
        .encoding_predefined(Name(b"WinAnsiEncoding"));
    pdf.type1_font(font_b_id)
        .base_font(Name(b"Helvetica-Bold"))
        .encoding_predefined(Name(b"WinAnsiEncoding"));
    if jpeg_size.is_some() {
        pdf.ext_graphics(gs_id)
            .non_stroking_alpha(spec.map_style.map_alpha())
            .stroking_alpha(spec.map_style.map_alpha());
    }
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
        paint_blank(&mut content, page_w, page_h);
        paint_jpeg(&mut content, page_w, page_h);
    } else {
        paint_blank(&mut content, page_w, page_h);
    }
    paint_overlays(&mut content, spec, page_w, page_h);
    pdf.stream(content_id, &content.finish());
    Ok(pdf.finish())
}

fn paint_jpeg(content: &mut Content, page_w: f32, page_h: f32) {
    content.save_state();
    content.set_parameters(GS);
    content.transform([page_w, 0.0, 0.0, page_h, 0.0, 0.0]);
    content.x_object(IMG);
    content.restore_state();
}

fn paint_blank(content: &mut Content, page_w: f32, page_h: f32) {
    fill_rgb(content, LAND);
    content.rect(0.0, 0.0, page_w, page_h);
    content.fill_nonzero();
}

fn paint_overlays(content: &mut Content, spec: &EnvelopeSpec, page_w: f32, page_h: f32) {
    let sx = page_w / PAGE_W;
    let sy = page_h / PAGE_H;
    let return_size = (9.0 * sy).clamp(8.0, 9.0);
    let return_lead = (11.0 * sy).clamp(9.5, 11.0);
    let dest_size = (11.0 * sy).clamp(9.0, 11.0);
    let dest_lead = (13.5 * sy).clamp(11.0, 13.5);

    let return_h = card_height(&spec.from, return_size, return_lead);
    let return_w = 210.0 * sx;
    let return_x = 16.0 * sx;
    let return_y = page_h - 16.0 * sy - return_h;

    let dest_h = card_height(&spec.to, dest_size, dest_lead);
    let dest_w = 260.0 * sx;
    let dest_x = 250.0 * sx;
    let dest_y = 92.0 * sy;

    fill_rgb(content, CARD);
    rounded_rect(content, return_x, return_y, return_w, return_h, 3.0);
    content.fill_nonzero();
    fill_rgb(content, CARD);
    rounded_rect(content, dest_x, dest_y, dest_w, dest_h, 3.5);
    content.fill_nonzero();

    write_address(
        content,
        &spec.from,
        return_x + 8.0 * sx,
        return_y + return_h - 14.0 * sy,
        return_size,
        return_lead,
        false,
    );
    write_address(
        content,
        &spec.to,
        dest_x + 12.0 * sx,
        dest_y + dest_h - 16.0 * sy,
        dest_size,
        dest_lead,
        true,
    );

    draw_stamp(content, page_w, page_h);
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
        let font = if delivery && i == 0 && addr.first_line_is_name() {
            FONT_B
        } else {
            FONT_R
        };
        let fitted = fit_chars(line, if delivery { 32 } else { 36 });
        show_text(content, font, size, x, y, &fitted);
    }
}

fn draw_stamp(content: &mut Content, page_w: f32, page_h: f32) {
    let w = 62.0;
    let h = 72.0;
    let x = page_w - 16.0 - w;
    let y = page_h - 16.0 - h;
    fill_rgb(content, CARD);
    rounded_rect(content, x, y, w, h, 2.0);
    content.fill_nonzero();
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
    use crate::geo::{LatLng, Route};
    use crate::maps::{EnvelopeSize, EnvelopeSpec, MapStyle};

    fn pdf_for(from: &str, to: &str) -> Vec<u8> {
        let spec = EnvelopeSpec::no_map(Address::parse(from).unwrap(), Address::parse(to).unwrap());
        render(&spec).unwrap()
    }

    #[test]
    fn stub_pdf_is_validish() {
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

    fn tiny_jpeg() -> Vec<u8> {
        let mut jpeg = vec![0xFF, 0xD8, 0xFF, 0xC0, 0x00, 0x0B, 0x08];
        jpeg.extend_from_slice(&8u16.to_be_bytes());
        jpeg.extend_from_slice(&8u16.to_be_bytes());
        jpeg.extend_from_slice(&[1, 1, 0x11, 0x00]);
        jpeg
    }

    fn spec_with_style(style: MapStyle) -> EnvelopeSpec {
        EnvelopeSpec {
            from: Address::parse("Ada\nMountain View, CA").unwrap(),
            to: Address::parse("Bob\nNew York, NY").unwrap(),
            route: Some(Route {
                points: vec![LatLng::new(37.4, -122.1), LatLng::new(40.7, -74.0)],
                distance_text: Some("2944 miles".into()),
                duration_text: Some("43 hr 22 min".into()),
            }),
            map_jpeg: Some(tiny_jpeg()),
            map_style: style,
            size: EnvelopeSize::Ten,
        }
    }

    #[test]
    fn hybrid_washes_more_than_google() {
        assert!(MapStyle::Hybrid.map_alpha() < MapStyle::Google.map_alpha());
        let google = render(&spec_with_style(MapStyle::Google)).unwrap();
        let hybrid = render(&spec_with_style(MapStyle::Hybrid)).unwrap();
        assert_ne!(google, hybrid);
        assert!(String::from_utf8_lossy(&google).contains("0.68"));
        assert!(String::from_utf8_lossy(&hybrid).contains("0.4"));
    }

    #[test]
    fn map_pdf_has_no_distance_or_extra_google_credit() {
        let pdf = render(&spec_with_style(MapStyle::Google)).unwrap();
        let s = String::from_utf8_lossy(&pdf);
        assert!(!s.contains("2944 miles"));
        assert!(!s.contains("43 hr 22 min"));
        assert!(!s.contains("Map data"));
    }

    fn media_box_wh(pdf: &[u8]) -> (f32, f32) {
        let s = String::from_utf8_lossy(pdf);
        let start = s.find("/MediaBox").expect("MediaBox");
        let slice = &s[start..];
        let lb = slice.find('[').expect("[");
        let rb = slice.find(']').expect("]");
        let nums: Vec<f32> = slice[lb + 1..rb]
            .split_whitespace()
            .map(|n| n.parse().expect("MediaBox number"))
            .collect();
        assert_eq!(nums.len(), 4);
        (nums[2] - nums[0], nums[3] - nums[1])
    }

    #[test]
    fn page_follows_envelope_size() {
        let from = Address::parse("Ada\nMountain View, CA").unwrap();
        let to = Address::parse("Bob\nNew York, NY").unwrap();
        let mut spec = EnvelopeSpec::no_map(from, to);
        let ten = render(&spec).unwrap();
        let (w, h) = media_box_wh(&ten);
        assert!((w - PAGE_W).abs() < 0.01);
        assert!((h - PAGE_H).abs() < 0.01);

        spec.size = EnvelopeSize::A7;
        let a7 = render(&spec).unwrap();
        let (aw, ah) = EnvelopeSize::A7.points();
        let (got_w, got_h) = media_box_wh(&a7);
        assert!((got_w - aw).abs() < 0.01);
        assert!((got_h - ah).abs() < 0.01);

        spec.size = EnvelopeSize::SixThreeQuarter;
        let small = render(&spec).unwrap();
        let (sw, sh) = EnvelopeSize::SixThreeQuarter.points();
        let (got_sw, got_sh) = media_box_wh(&small);
        assert!((got_sw - sw).abs() < 0.01);
        assert!((got_sh - sh).abs() < 0.01);
        assert_ne!(media_box_wh(&ten), media_box_wh(&small));
    }

    #[test]
    fn dest_card_fits_beside_stamp() {
        for size in EnvelopeSize::ALL {
            let (w, _) = size.points();
            let sx = w / PAGE_W;
            let dest_right = (250.0 + 260.0) * sx;
            let stamp_left = w - 16.0 - 62.0;
            assert!(
                dest_right < stamp_left,
                "{size:?}: dest right {dest_right} overlaps stamp at {stamp_left}"
            );
        }
    }
}
