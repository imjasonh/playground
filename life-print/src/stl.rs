//! Binary STL sanity checks.
//!
//! life-lab always emits binary STLs (`life_stl::stl_bytes`). Slant's slicer
//! fetches a public URL, so we refuse garbage / empty meshes before paying for
//! a round-trip to their API.

/// Why an STL body was rejected.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StlError {
    TooShort,
    Truncated { expected: usize, got: usize },
    Empty,
    Ascii,
}

impl StlError {
    pub fn message(&self) -> String {
        match self {
            StlError::TooShort => "STL too short to be a binary mesh".into(),
            StlError::Truncated { expected, got } => {
                format!("STL truncated: expected {expected} bytes, got {got}")
            }
            StlError::Empty => "STL has zero triangles".into(),
            StlError::Ascii => "ASCII STL is not supported; send a binary STL".into(),
        }
    }
}

/// Validate a binary STL and return its triangle count.
///
/// Accepts files that are exactly `84 + n*50` bytes, or slightly longer
/// (some exporters append padding). Rejects ASCII STLs that begin with
/// `solid` and look like text.
pub fn validate_binary_stl(bytes: &[u8]) -> Result<u32, StlError> {
    // ASCII STLs typically start with "solid " and are newline-delimited text.
    // Check before the length gate so short ASCII samples still get a clear
    // error (binary STLs that begin with "solid" in the 80-byte header are
    // distinguished by `looks_like_ascii_stl`'s printable-ratio heuristic).
    if looks_like_ascii_stl(bytes) {
        return Err(StlError::Ascii);
    }

    if bytes.len() < 84 {
        return Err(StlError::TooShort);
    }

    let n = u32::from_le_bytes(bytes[80..84].try_into().expect("4 bytes"));
    if n == 0 {
        return Err(StlError::Empty);
    }
    let expected = 84usize.saturating_add((n as usize).saturating_mul(50));
    if bytes.len() < expected {
        return Err(StlError::Truncated {
            expected,
            got: bytes.len(),
        });
    }
    // Reject absurd trailing garbage (more than one extra triangle's worth).
    if bytes.len() > expected + 50 {
        return Err(StlError::Truncated {
            expected,
            got: bytes.len(),
        });
    }
    Ok(n)
}

fn looks_like_ascii_stl(bytes: &[u8]) -> bool {
    if bytes.len() < 6 {
        return false;
    }
    let head = &bytes[..6];
    if !head.eq_ignore_ascii_case(b"solid ") && !head.eq_ignore_ascii_case(b"solid\n") {
        return false;
    }
    // Sample up to 512 bytes; if nearly all are printable / whitespace, ASCII.
    let sample = &bytes[..bytes.len().min(512)];
    if sample.is_empty() {
        return false;
    }
    let printable = sample
        .iter()
        .filter(|&&b| b == b'\n' || b == b'\r' || b == b'\t' || (0x20..=0x7e).contains(&b))
        .count();
    printable * 100 / sample.len() > 90
}

#[cfg(test)]
mod tests {
    use super::*;

    fn binary_stl(triangles: u32) -> Vec<u8> {
        let mut out = vec![0u8; 80];
        out.extend_from_slice(&triangles.to_le_bytes());
        for i in 0..triangles {
            // 12 floats (normal + 3 verts) + 2-byte attribute = 50 bytes
            let mut tri = vec![0u8; 50];
            tri[0] = (i & 0xff) as u8;
            out.extend_from_slice(&tri);
        }
        out
    }

    #[test]
    fn accepts_minimal_binary() {
        assert_eq!(validate_binary_stl(&binary_stl(1)).unwrap(), 1);
        assert_eq!(validate_binary_stl(&binary_stl(3)).unwrap(), 3);
    }

    #[test]
    fn rejects_empty_and_short() {
        assert_eq!(validate_binary_stl(&[]).unwrap_err(), StlError::TooShort);
        assert_eq!(
            validate_binary_stl(&binary_stl(0)).unwrap_err(),
            StlError::Empty
        );
    }

    #[test]
    fn rejects_truncated() {
        let mut bytes = binary_stl(2);
        bytes.truncate(84 + 50); // one triangle short
        match validate_binary_stl(&bytes).unwrap_err() {
            StlError::Truncated { expected, got } => {
                assert_eq!(expected, 84 + 100);
                assert_eq!(got, 84 + 50);
            }
            other => panic!("unexpected {other:?}"),
        }
    }

    #[test]
    fn rejects_ascii() {
        let ascii = b"solid name\n facet normal 0 0 0\n  outer loop\n   vertex 0 0 0\n endsolid\n";
        assert_eq!(validate_binary_stl(ascii).unwrap_err(), StlError::Ascii);
    }
}
