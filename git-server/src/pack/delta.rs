//! Delta encoding primitives (gitformat-pack(5) "Deltified representation").

/// Parse the little-endian base-128 varint used for delta base/result sizes.
/// Returns (value, bytes consumed) or `None` if truncated.
pub fn parse_size_varint(data: &[u8]) -> Option<(u64, usize)> {
    let mut value: u64 = 0;
    let mut shift = 0;
    for (i, &b) in data.iter().enumerate() {
        value |= u64::from(b & 0x7f) << shift;
        if b & 0x80 == 0 {
            return Some((value, i + 1));
        }
        shift += 7;
        if shift > 63 {
            return None;
        }
    }
    None
}

/// Apply a git delta to `base`, producing the target object content.
pub fn apply_delta(base: &[u8], delta: &[u8]) -> Result<Vec<u8>, String> {
    let (base_size, n) = parse_size_varint(delta).ok_or("delta: truncated base size")?;
    if base_size != base.len() as u64 {
        return Err(format!(
            "delta: base size mismatch (expected {base_size}, have {})",
            base.len()
        ));
    }
    let mut pos = n;
    let (result_size, n) =
        parse_size_varint(&delta[pos..]).ok_or("delta: truncated result size")?;
    pos += n;

    let mut out = Vec::with_capacity(result_size as usize);
    while pos < delta.len() {
        let op = delta[pos];
        pos += 1;
        if op & 0x80 != 0 {
            // Copy from base: bits 0-3 select offset bytes, bits 4-6 size bytes.
            let mut offset: u64 = 0;
            for i in 0..4 {
                if op & (1 << i) != 0 {
                    let b = *delta.get(pos).ok_or("delta: truncated copy offset")?;
                    offset |= u64::from(b) << (8 * i);
                    pos += 1;
                }
            }
            let mut size: u64 = 0;
            for i in 0..3 {
                if op & (1 << (4 + i)) != 0 {
                    let b = *delta.get(pos).ok_or("delta: truncated copy size")?;
                    size |= u64::from(b) << (8 * i);
                    pos += 1;
                }
            }
            if size == 0 {
                size = 0x10000;
            }
            let start = offset as usize;
            let end = start
                .checked_add(size as usize)
                .filter(|&e| e <= base.len())
                .ok_or("delta: copy out of range")?;
            out.extend_from_slice(&base[start..end]);
        } else if op != 0 {
            // Insert literal bytes.
            let len = op as usize;
            let end = pos.checked_add(len).filter(|&e| e <= delta.len());
            let end = end.ok_or("delta: truncated insert")?;
            out.extend_from_slice(&delta[pos..end]);
            pos = end;
        } else {
            return Err("delta: reserved opcode 0".into());
        }
    }
    if out.len() as u64 != result_size {
        return Err(format!(
            "delta: result size mismatch (expected {result_size}, got {})",
            out.len()
        ));
    }
    Ok(out)
}

/// Encode the size varint used in delta headers.
pub fn encode_size_varint(mut value: u64) -> Vec<u8> {
    let mut out = Vec::new();
    loop {
        let mut b = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            b |= 0x80;
        }
        out.push(b);
        if value == 0 {
            return out;
        }
    }
}

/// Build a trivial delta that represents `target` with no copies (one or more
/// insert ops). Used only in tests; real deltas come from clients.
pub fn literal_delta(base_len: usize, target: &[u8]) -> Vec<u8> {
    let mut out = encode_size_varint(base_len as u64);
    out.extend_from_slice(&encode_size_varint(target.len() as u64));
    for chunk in target.chunks(127) {
        out.push(chunk.len() as u8);
        out.extend_from_slice(chunk);
    }
    out
}

/// Parse a pack *entry header*: type (3 bits) and uncompressed size, in the
/// MSB-continued little-endian layout. Returns (type, size, bytes consumed).
pub fn parse_entry_header(data: &[u8]) -> Option<(u8, u64, usize)> {
    let first = *data.first()?;
    let ty = (first >> 4) & 0x7;
    let mut size = u64::from(first & 0x0f);
    let mut shift = 4;
    let mut pos = 1;
    let mut byte = first;
    while byte & 0x80 != 0 {
        byte = *data.get(pos)?;
        size |= u64::from(byte & 0x7f) << shift;
        shift += 7;
        pos += 1;
        if shift > 63 {
            return None;
        }
    }
    Some((ty, size, pos))
}

/// Encode a pack entry header.
pub fn encode_entry_header(ty: u8, mut size: u64) -> Vec<u8> {
    let mut out = Vec::new();
    let mut b = (ty << 4) | (size & 0x0f) as u8;
    size >>= 4;
    while size != 0 {
        out.push(b | 0x80);
        b = (size & 0x7f) as u8;
        size >>= 7;
    }
    out.push(b);
    out
}

/// Parse the OFS_DELTA relative-offset encoding (big-endian 7-bit groups with
/// the +1 bias). Returns (relative offset, bytes consumed).
pub fn parse_ofs_delta_offset(data: &[u8]) -> Option<(u64, usize)> {
    let mut b = *data.first()?;
    let mut value = u64::from(b & 0x7f);
    let mut pos = 1;
    while b & 0x80 != 0 {
        b = *data.get(pos)?;
        value = value
            .checked_add(1)?
            .checked_mul(128)?
            .checked_add(u64::from(b & 0x7f))?;
        pos += 1;
    }
    Some((value, pos))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn size_varint_roundtrip() {
        for v in [0u64, 1, 127, 128, 300, 65535, 1 << 40] {
            let enc = encode_size_varint(v);
            assert_eq!(parse_size_varint(&enc), Some((v, enc.len())), "v={v}");
        }
    }

    #[test]
    fn entry_header_roundtrip() {
        for (ty, size) in [(1u8, 0u64), (3, 15), (3, 16), (2, 12345), (7, 1 << 33)] {
            let enc = encode_entry_header(ty, size);
            assert_eq!(
                parse_entry_header(&enc),
                Some((ty, size, enc.len())),
                "ty={ty} size={size}"
            );
        }
    }

    #[test]
    fn apply_literal_delta() {
        let base = b"the quick brown fox";
        let target = vec![42u8; 500];
        let delta = literal_delta(base.len(), &target);
        assert_eq!(apply_delta(base, &delta).unwrap(), target);
    }

    #[test]
    fn apply_copy_delta() {
        // Hand-build: copy bytes 4..9 of base, insert "!", copy 0..3.
        let base = b"abcdthe quick";
        let mut delta = encode_size_varint(base.len() as u64);
        delta.extend_from_slice(&encode_size_varint(5 + 1 + 3));
        // copy: offset=4 (1 offset byte), size=5 (1 size byte)
        delta.extend_from_slice(&[0x80 | 0x01 | 0x10, 4, 5]);
        delta.extend_from_slice(&[1, b'!']);
        // copy offset=0 size=3: offset omitted (0), size byte present
        delta.extend_from_slice(&[0x80 | 0x10, 3]);
        assert_eq!(apply_delta(base, &delta).unwrap(), b"the q!abc");
    }

    #[test]
    fn ofs_offset_examples() {
        // Single byte: value as-is.
        assert_eq!(parse_ofs_delta_offset(&[0x05]), Some((5, 1)));
        // Two bytes: ((0x80&0x7f)+1)*128 + 0 = 128 for [0x80, 0x00].
        assert_eq!(parse_ofs_delta_offset(&[0x80, 0x00]), Some((128, 2)));
    }

    #[test]
    fn bad_deltas_rejected() {
        assert!(apply_delta(b"abc", &[]).is_err());
        // Base size mismatch.
        let delta = literal_delta(99, b"x");
        assert!(apply_delta(b"abc", &delta).is_err());
        // Copy out of range.
        let mut delta = encode_size_varint(3);
        delta.extend_from_slice(&encode_size_varint(10));
        delta.extend_from_slice(&[0x80 | 0x10, 10]); // copy size 10 from 3-byte base
        assert!(apply_delta(b"abc", &delta).is_err());
    }
}
