//! Builds boot-state records, slot manifests, and image headers, valid and
//! mutated, decodes each with `c3-verify`, and prints one line per input
//! with the result. `c3-boot-proofs`'s `decode-check` reads the same lines,
//! decodes them with the Lean specification, and must print identical lines.
//!
//! The lines are:
//!
//! - `record HEX | ok STATE` or `record HEX | err`
//! - `read HEX HEX | STATE copy=A`, `copy=B`, or `copy=-`
//! - `manifest HEX | ok i=OFF,LEN b=OFF,LEN c=OFF,LEN l=OFF,LEN` or `| err`
//! - `image LEN HEX | ok sv=N e=N segs=K@ADDR+OFF:LEN,...` or `| err`
//!
//! where `STATE` is `g=N p=A|B t=-|A0..B3 c=N`.

// A host-side test generator, not device code: its arithmetic and indexing
// work on values it chose itself.
#![allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]

use std::io::BufWriter;
use std::io::Write;

use c3_verify::bootstate;
use c3_verify::bootstate::Slot;
use c3_verify::bootstate::State;
use c3_verify::bootstate::Trial;
use c3_verify::image::SegmentKind;

const CASES: usize = 20_000;
const PAGE: u32 = 0x1_0000;

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    fn chance(&mut self, percent: u64) -> bool {
        self.below(100) < percent
    }

    /// A value near `v`: off by one, four, or a page, or anything.
    fn near(&mut self, v: u32) -> u32 {
        match self.below(8) {
            0 => v.wrapping_add(1),
            1 => v.wrapping_sub(1),
            2 => v.wrapping_add(4),
            3 => v.wrapping_sub(4),
            4 => v.wrapping_add(PAGE),
            5 => v.wrapping_sub(PAGE),
            6 => u32::MAX - self.below(0x2_0000) as u32,
            _ => self.next() as u32,
        }
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn slot_name(s: Slot) -> &'static str {
    match s {
        Slot::A => "A",
        Slot::B => "B",
    }
}

fn show_state(s: &State) -> String {
    let trial = s.trial.map_or_else(
        || "-".to_string(),
        |t| format!("{}{}", slot_name(t.slot), t.boots_left),
    );
    let c = u8::from(s.is_confirmed(Slot::A)) | (u8::from(s.is_confirmed(Slot::B)) << 1);
    format!(
        "g={} p={} t={} c={c}",
        s.generation,
        slot_name(s.preferred),
        trial
    )
}

fn random_state(rng: &mut Rng) -> State {
    let mut s = State::DEFAULT;
    s.generation = match rng.below(4) {
        0 => 0,
        1 => u32::MAX,
        _ => rng.next() as u32,
    };
    s.preferred = if rng.chance(50) { Slot::A } else { Slot::B };
    s.trial = if rng.chance(50) {
        None
    } else {
        Some(Trial {
            slot: if rng.chance(50) { Slot::A } else { Slot::B },
            boots_left: rng.below(4) as u8,
        })
    };
    if rng.chance(50) {
        s = s.with_confirmed(Slot::A);
    }
    if rng.chance(50) {
        s = s.with_confirmed(Slot::B);
    }
    s
}

/// A record: valid, then for most, one change, often with the CRC fixed so
/// the field rules get tested.
fn record(rng: &mut Rng) -> [u8; bootstate::RECORD_LEN] {
    let mut r = bootstate::encode(&random_state(rng));
    if rng.chance(40) {
        return r;
    }
    let at = rng.below(32) as usize;
    r[at] = match rng.below(4) {
        0 => r[at] ^ 1,
        1 => 0xFF,
        2 => rng.below(5) as u8,
        _ => rng.next() as u8,
    };
    if at < 28 && rng.chance(80) {
        let crc = bootstate::crc32(&r[..28]).to_le_bytes();
        r[28..].copy_from_slice(&crc);
    }
    r
}

fn manifest(rng: &mut Rng) -> Vec<u8> {
    let image_len = 37 + rng.below(0x2_0000) as u32;
    let bundle_off = 0x1_0000 + image_len + rng.below(8) as u32;
    let bundle_len = 49 + rng.below(16_000) as u32;
    let chain_off = bundle_off + bundle_len + rng.below(8) as u32;
    let chain_len = 8 + rng.below(2_000) as u32;
    let blob_off = chain_off + chain_len + rng.below(8) as u32;
    let blob_len = 443 + rng.below(3_600) as u32;
    let mut fields = [
        0x1_0000, image_len, bundle_off, bundle_len, chain_off, chain_len, blob_off, blob_len,
    ];
    let bounds = [37, 0x1D_0000, 49, 16_384, 8, 2_048, 443, 4_096];
    if rng.chance(50) {
        let i = rng.below(8) as usize;
        fields[i] = if i % 2 == 1 && rng.chance(50) {
            let (lo, hi) = (bounds[i - 1], bounds[i]);
            [lo - 1, lo, hi, hi + 1][rng.below(4) as usize]
        } else {
            rng.near(fields[i])
        };
    }
    let mut out = b"C3SL".to_vec();
    out.extend_from_slice(&1u16.to_le_bytes());
    out.extend_from_slice(&[0, 0]);
    for f in fields {
        out.extend_from_slice(&f.to_le_bytes());
    }
    if rng.chance(5) {
        let at = rng.below(8) as usize;
        out[at] ^= 1 << rng.below(8);
    }
    // A manifest is exactly 40 bytes.
    match rng.below(40) {
        0 => out.push(0),
        1 => {
            out.pop();
        }
        _ => {}
    }
    out
}

/// An image header with up to four valid segments, then often one change.
/// One in twenty has the most segments, sixteen.
fn image(rng: &mut Rng) -> (u32, Vec<u8>) {
    if rng.chance(5) {
        return image16(rng);
    }
    let mut segs: Vec<(u8, u32, u32, u32)> = Vec::new();
    let mut ram_data_at = 0x3FC8_8000u32;
    if rng.chance(70) {
        segs.push((3, 0x4038_0000, 0, 4 * (1 + rng.below(0x800) as u32)));
        ram_data_at = 0x3FC8_0000 + segs[0].3.next_multiple_of(0x1000) + 0x1000;
    }
    if rng.chance(15) {
        // The data-bus alias of RAM code, which overlaps it.
        ram_data_at = 0x3FC8_0000 + 4 * rng.below(4) as u32;
    }
    if rng.chance(60) {
        segs.push((4, ram_data_at, 0, 4 * (1 + rng.below(0x400) as u32)));
    }
    let flash_data = rng.chance(60);
    let flash_code = rng.chance(50) || segs.iter().all(|s| s.0 != 3);
    if flash_data {
        segs.push((2, 0x3C00_0000, 0, PAGE * (1 + rng.below(2) as u32)));
    }
    if flash_code {
        // Flash code and data share the cache's linear address space, so
        // code at the start of its window can collide with data at the start
        // of its own.
        let at = if rng.chance(25) {
            0x4200_0000
        } else {
            0x4210_0000
        };
        segs.push((1, at, 0, PAGE * (1 + rng.below(2) as u32)));
    }
    let table_end = 20 + 16 * segs.len() as u32;
    let mut pos = table_end.next_multiple_of(4);
    for s in segs.iter_mut() {
        if s.0 <= 2 {
            pos = pos.next_multiple_of(PAGE);
        }
        s.2 = pos;
        pos += s.3;
    }
    let mut image_len = pos;
    let exec = segs
        .iter()
        .find(|s| s.0 == 1 || s.0 == 3)
        .copied()
        .unwrap_or(segs[0]);
    let mut entry = exec.1 + 2 * rng.below(u64::from(exec.3 / 2)) as u32;
    let mut sv = rng.below(17) as u8;
    let mut count = segs.len() as u8;
    if rng.chance(55) {
        match rng.below(8) {
            0 => {
                let i = rng.below(segs.len() as u64) as usize;
                segs[i].1 = rng.near(segs[i].1);
            }
            1 => {
                let i = rng.below(segs.len() as u64) as usize;
                segs[i].2 = rng.near(segs[i].2);
            }
            2 => {
                let i = rng.below(segs.len() as u64) as usize;
                segs[i].3 = rng.near(segs[i].3);
            }
            3 => {
                let i = rng.below(segs.len() as u64) as usize;
                segs[i].0 = rng.below(6) as u8;
            }
            4 => entry = rng.near(entry),
            5 => image_len = rng.near(image_len),
            6 => sv = 16 + rng.below(3) as u8,
            _ => count = rng.below(18) as u8,
        }
    }
    let mut out = b"C3IM".to_vec();
    out.extend_from_slice(&1u16.to_le_bytes());
    out.extend_from_slice(&5u16.to_le_bytes());
    out.push(sv);
    out.push(count);
    out.extend_from_slice(&[0, 0]);
    out.extend_from_slice(&entry.to_le_bytes());
    out.extend_from_slice(&image_len.to_le_bytes());
    for s in &segs {
        out.push(s.0);
        out.extend_from_slice(&[0, 0, 0]);
        out.extend_from_slice(&s.1.to_le_bytes());
        out.extend_from_slice(&s.2.to_le_bytes());
        out.extend_from_slice(&s.3.to_le_bytes());
    }
    if rng.chance(5) {
        let at = rng.below(out.len() as u64) as usize;
        out[at] ^= 1 << rng.below(8);
    }
    let header_len = if rng.chance(5) {
        rng.below(out.len() as u64) as usize
    } else {
        out.len()
    };
    out.truncate(header_len);
    (image_len, out)
}

/// A header with sixteen RAM segments: code first, then data, packed one
/// after another, sometimes with one changed.
fn image16(rng: &mut Rng) -> (u32, Vec<u8>) {
    let mut segs = vec![(3u8, 0x4038_0000u32, 0u32, 0x100u32)];
    let mut addr = 0x3FC9_0000u32;
    for _ in 1..16 {
        let len = 4 * (1 + rng.below(16) as u32);
        segs.push((4, addr, 0, len));
        addr += len;
    }
    let mut pos = 20 + 16 * 16;
    for s in segs.iter_mut() {
        s.2 = pos;
        pos += s.3;
    }
    if rng.chance(50) {
        let i = rng.below(16) as usize;
        match rng.below(3) {
            0 => segs[i].1 = rng.near(segs[i].1),
            1 => segs[i].2 = rng.near(segs[i].2),
            _ => segs[i].3 = rng.near(segs[i].3),
        }
    }
    let mut out = b"C3IM".to_vec();
    out.extend_from_slice(&1u16.to_le_bytes());
    out.extend_from_slice(&5u16.to_le_bytes());
    out.push(0);
    out.push(16);
    out.extend_from_slice(&[0, 0]);
    out.extend_from_slice(&0x4038_0000u32.to_le_bytes());
    out.extend_from_slice(&pos.to_le_bytes());
    for s in &segs {
        out.push(s.0);
        out.extend_from_slice(&[0, 0, 0]);
        out.extend_from_slice(&s.1.to_le_bytes());
        out.extend_from_slice(&s.2.to_le_bytes());
        out.extend_from_slice(&s.3.to_le_bytes());
    }
    (pos, out)
}

fn kind_digit(k: SegmentKind) -> u8 {
    match k {
        SegmentKind::FlashCode => 1,
        SegmentKind::FlashData => 2,
        SegmentKind::RamCode => 3,
        SegmentKind::RamData => 4,
    }
}

fn main() -> std::io::Result<()> {
    let mut rng = Rng(0x0C3B_DEC0);
    let mut out = BufWriter::new(std::io::stdout().lock());
    let mut records = Vec::new();
    for _ in 0..CASES {
        let r = record(&mut rng);
        let result = bootstate::decode(&r)
            .map_or_else(|_| "err".to_string(), |s| format!("ok {}", show_state(&s)));
        writeln!(out, "record {} | {result}", hex(&r))?;
        records.push(r);
    }
    for _ in 0..CASES / 4 {
        let a = records[rng.below(records.len() as u64) as usize];
        let b = records[rng.below(records.len() as u64) as usize];
        let current = bootstate::read(&a, &b);
        let copy = match current.copy {
            Some(bootstate::Copy::A) => "A",
            Some(bootstate::Copy::B) => "B",
            None => "-",
        };
        writeln!(
            out,
            "read {} {} | {} copy={copy}",
            hex(&a),
            hex(&b),
            show_state(&current.state)
        )?;
    }
    for _ in 0..CASES {
        let m = manifest(&mut rng);
        let result = c3_verify::manifest::parse(&m).map_or_else(
            |_| "err".to_string(),
            |m| {
                format!(
                    "ok i={},{} b={},{} c={},{} l={},{}",
                    m.image.offset,
                    m.image.length,
                    m.bundle.offset,
                    m.bundle.length,
                    m.chain.offset,
                    m.chain.length,
                    m.blob.offset,
                    m.blob.length
                )
            },
        );
        writeln!(out, "manifest {} | {result}", hex(&m))?;
    }
    for _ in 0..CASES {
        let (len, bytes) = image(&mut rng);
        let result = c3_verify::image::parse(&bytes, len).map_or_else(
            |_| "err".to_string(),
            |h| {
                let segs: Vec<String> = h
                    .segments()
                    .iter()
                    .map(|s| {
                        format!(
                            "{}@{}+{}:{}",
                            kind_digit(s.kind),
                            s.address,
                            s.offset,
                            s.length
                        )
                    })
                    .collect();
                format!(
                    "ok sv={} e={} segs={}",
                    h.security_version,
                    h.entry_point,
                    segs.join(",")
                )
            },
        );
        writeln!(out, "image {len} {} | {result}", hex(&bytes))?;
    }
    out.flush()
}
