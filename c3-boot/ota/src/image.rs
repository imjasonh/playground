//! Packs an application ELF into the signed image format and the
//! bootloader ELF into the ROM's ESP image format.

use c3_verify::layout;
use object::Object;
use object::ObjectSegment;

/// A loadable piece of an ELF: its address and file bytes.
struct Load {
    address: u32,
    data: Vec<u8>,
}

fn loads(elf: &[u8]) -> Result<(u32, Vec<Load>), String> {
    let file = object::File::parse(elf).map_err(|e| e.to_string())?;
    let entry = u32::try_from(file.entry()).map_err(|_| "entry point above 4 GiB")?;
    let mut out = Vec::new();
    for seg in file.segments() {
        let data = seg.data().map_err(|e| e.to_string())?;
        if data.is_empty() {
            continue;
        }
        let address = u32::try_from(seg.address()).map_err(|_| "segment above 4 GiB")?;
        out.push(Load {
            address,
            data: data.to_vec(),
        });
    }
    out.sort_by_key(|l| l.address);
    Ok((entry, out))
}

fn kind_of(address: u32) -> Result<u8, String> {
    if layout::FLASH_CODE.contains_range(address, 1) {
        Ok(1)
    } else if layout::FLASH_DATA.contains_range(address, 1) {
        Ok(2)
    } else if layout::RAM_CODE.contains_range(address, 1) {
        Ok(3)
    } else if layout::RAM_DATA.contains_range(address, 1) {
        Ok(4)
    } else {
        Err(format!(
            "segment at {address:#x} is outside every allowed region"
        ))
    }
}

fn align_up(n: usize, to: usize) -> usize {
    n.div_ceil(to) * to
}

/// Packs `elf`'s loadable segments into a signed image with
/// `security_version`. RAM segments come first, padded to four bytes. Each
/// flash segment starts on the next 64 KiB boundary.
pub fn pack(elf: &[u8], security_version: u8) -> Result<Vec<u8>, String> {
    let (entry, loads) = loads(elf)?;
    let mut ram = Vec::new();
    let mut flash = Vec::new();
    for l in loads {
        let kind = kind_of(l.address)?;
        if kind <= 2 {
            flash.push((kind, l))
        } else {
            ram.push((kind, l))
        }
    }
    let count = ram.len() + flash.len();
    let header_len = 20 + 16 * count;
    let mut table = Vec::new();
    let mut body: Vec<u8> = Vec::new();
    let mut pos = align_up(header_len, 4);
    let place =
        |kind: u8, l: &Load, offset: usize, table: &mut Vec<u8>, body: &mut Vec<u8>| -> usize {
            let mut data = l.data.clone();
            if kind >= 3 {
                data.resize(align_up(data.len(), 4), 0);
            }
            body.resize(offset - header_len, 0xFF);
            body.extend_from_slice(&data);
            table.push(kind);
            table.extend_from_slice(&[0, 0, 0]);
            table.extend_from_slice(&l.address.to_le_bytes());
            table.extend_from_slice(&(offset as u32).to_le_bytes());
            table.extend_from_slice(&(data.len() as u32).to_le_bytes());
            offset + data.len()
        };
    for (kind, l) in &ram {
        pos = place(*kind, l, pos, &mut table, &mut body);
    }
    for (kind, l) in &flash {
        if l.address % layout::FLASH_PAGE != 0 {
            return Err(format!(
                "flash segment at {:#x} isn't 64 KiB aligned",
                l.address
            ));
        }
        let offset = align_up(pos, layout::FLASH_PAGE as usize);
        pos = place(*kind, l, offset, &mut table, &mut body);
    }
    let image_len = u32::try_from(pos).map_err(|_| "image too large")?;
    let mut out = b"C3IM".to_vec();
    out.extend_from_slice(&1u16.to_le_bytes());
    out.extend_from_slice(&c3_verify::image::CHIP_ID_ESP32C3.to_le_bytes());
    out.push(security_version);
    out.push(u8::try_from(count).map_err(|_| "too many segments")?);
    out.extend_from_slice(&[0, 0]);
    out.extend_from_slice(&entry.to_le_bytes());
    out.extend_from_slice(&image_len.to_le_bytes());
    out.extend_from_slice(&table);
    out.extend_from_slice(&body);
    c3_verify::image::parse(&out, image_len)
        .map_err(|e| format!("packed image fails its own checks: {e:?}"))?;
    Ok(out)
}

/// Converts the bootloader ELF into the ESP32-C3 ROM's image format, with
/// the SHA-256 digest appended, for flash offset 0.
pub fn esp_image(elf: &[u8]) -> Result<Vec<u8>, String> {
    let (entry, loads) = loads(elf)?;
    let mut out = vec![
        0xE9,
        u8::try_from(loads.len()).map_err(|_| "too many segments")?,
        0x02, // DIO
        0x20, // 4 MB, 40 MHz
    ];
    out.extend_from_slice(&entry.to_le_bytes());
    out.extend_from_slice(&[0xEE, 0, 0, 0]);
    out.extend_from_slice(&c3_verify::image::CHIP_ID_ESP32C3.to_le_bytes());
    out.push(0);
    out.extend_from_slice(&0u16.to_le_bytes());
    out.extend_from_slice(&199u16.to_le_bytes());
    out.extend_from_slice(&[0, 0, 0, 0]);
    out.push(1);
    let mut checksum = 0xEFu8;
    for l in &loads {
        let mut data = l.data.clone();
        data.resize(align_up(data.len(), 4), 0);
        out.extend_from_slice(&l.address.to_le_bytes());
        out.extend_from_slice(&(data.len() as u32).to_le_bytes());
        for b in &data {
            checksum ^= b;
        }
        out.extend_from_slice(&data);
    }
    while out.len() % 16 != 15 {
        out.push(0);
    }
    out.push(checksum);
    let digest = c3_crypto::sha256(&out);
    out.extend_from_slice(&digest);
    Ok(out)
}
