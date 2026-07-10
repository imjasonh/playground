//! Line diff (Myers O(ND)) used by the blame engine and tree comparison.
//!
//! Operates on line hashes, so a diff over two versions of a large file costs
//! one pass to split + hash and then the classic greedy Myers walk. Only line
//! *matches* are reported — exactly what blame needs (matched lines inherit
//! their attribution from the older version; unmatched lines were introduced
//! by the newer commit).

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

/// Split into lines, keeping semantics stable for files without a trailing
/// newline (the final fragment is still a line).
pub fn split_lines(data: &[u8]) -> Vec<&[u8]> {
    if data.is_empty() {
        return Vec::new();
    }
    let mut out = Vec::new();
    let mut start = 0;
    for (i, &b) in data.iter().enumerate() {
        if b == b'\n' {
            out.push(&data[start..=i]);
            start = i + 1;
        }
    }
    if start < data.len() {
        out.push(&data[start..]);
    }
    out
}

fn hash_line(line: &[u8]) -> u64 {
    let mut h = DefaultHasher::new();
    line.hash(&mut h);
    h.finish()
}

/// Compute matched line pairs `(old_index, new_index)` between two texts, in
/// increasing order on both sides.
pub fn match_lines(old: &[u8], new: &[u8]) -> Vec<(usize, usize)> {
    let a: Vec<u64> = split_lines(old).iter().map(|l| hash_line(l)).collect();
    let b: Vec<u64> = split_lines(new).iter().map(|l| hash_line(l)).collect();
    myers_matches(&a, &b)
}

/// Greedy Myers diff returning the matched (common) index pairs.
fn myers_matches(a: &[u64], b: &[u64]) -> Vec<(usize, usize)> {
    let n = a.len() as isize;
    let m = b.len() as isize;
    if n == 0 || m == 0 {
        return Vec::new();
    }
    // Edit-distance cap: beyond this the versions are effectively rewrites,
    // and attributing every line to the newer commit is both correct-enough
    // and avoids the O(d^2) trace memory on pathological inputs.
    let max = (n + m).min(10_000);
    let offset = max;
    // v[k + offset] = furthest x on diagonal k.
    let mut v = vec![0isize; (2 * max + 1) as usize];
    // Trace of v arrays per d, for backtracking.
    let mut trace: Vec<Vec<isize>> = Vec::new();

    let mut found_d = None;
    'outer: for d in 0..=max {
        trace.push(v.clone());
        let mut k = -d;
        while k <= d {
            let idx = (k + offset) as usize;
            let mut x = if k == -d || (k != d && v[idx - 1] < v[idx + 1]) {
                v[idx + 1]
            } else {
                v[idx - 1] + 1
            };
            let mut y = x - k;
            while x < n && y < m && a[x as usize] == b[y as usize] {
                x += 1;
                y += 1;
            }
            v[idx] = x;
            if x >= n && y >= m {
                found_d = Some(d);
                break 'outer;
            }
            k += 2;
        }
    }

    // Distance cap exceeded: treat as a rewrite (no matches).
    if found_d.is_none() {
        return Vec::new();
    }
    let mut matches = Vec::new();
    let (mut x, mut y) = (n, m);
    for (d, vd) in trace.iter().enumerate().rev() {
        let d = d as isize;
        let k = x - y;
        let idx = (k + offset) as usize;
        let prev_k = if k == -d || (k != d && vd[idx - 1] < vd[idx + 1]) {
            k + 1
        } else {
            k - 1
        };
        let prev_x = vd[(prev_k + offset) as usize];
        let prev_y = prev_x - prev_k;
        while x > prev_x && y > prev_y {
            matches.push(((x - 1) as usize, (y - 1) as usize));
            x -= 1;
            y -= 1;
        }
        x = prev_x;
        y = prev_y;
    }
    matches.reverse();
    matches
}

#[cfg(test)]
mod tests {
    use super::*;

    fn matched_pairs(old: &str, new: &str) -> Vec<(usize, usize)> {
        match_lines(old.as_bytes(), new.as_bytes())
    }

    #[test]
    fn split_handles_trailing_newline() {
        assert_eq!(split_lines(b"a\nb\n").len(), 2);
        assert_eq!(split_lines(b"a\nb").len(), 2);
        assert_eq!(split_lines(b"").len(), 0);
    }

    #[test]
    fn identical_texts_match_fully() {
        let m = matched_pairs("a\nb\nc\n", "a\nb\nc\n");
        assert_eq!(m, vec![(0, 0), (1, 1), (2, 2)]);
    }

    #[test]
    fn insertion_shifts_matches() {
        let m = matched_pairs("a\nc\n", "a\nb\nc\n");
        assert_eq!(m, vec![(0, 0), (1, 2)]);
    }

    #[test]
    fn deletion_matches_remainder() {
        let m = matched_pairs("a\nb\nc\n", "a\nc\n");
        assert_eq!(m, vec![(0, 0), (2, 1)]);
    }

    #[test]
    fn disjoint_texts_share_nothing() {
        let m = matched_pairs("x\ny\n", "p\nq\nr\n");
        assert!(m.is_empty());
    }

    #[test]
    fn modified_middle_line() {
        let m = matched_pairs("one\ntwo\nthree\n", "one\nTWO\nthree\n");
        assert_eq!(m, vec![(0, 0), (2, 2)]);
    }

    #[test]
    fn matches_are_monotonic_on_random_edits() {
        // Sanity check monotonicity + validity on a synthetic case.
        let mut old = String::new();
        let mut new = String::new();
        for i in 0..200 {
            old.push_str(&format!("line{i}\n"));
            if i % 7 == 0 {
                continue;
            }
            if i % 13 == 0 {
                new.push_str(&format!("edited{i}\n"));
            } else {
                new.push_str(&format!("line{i}\n"));
            }
        }
        let m = match_lines(old.as_bytes(), new.as_bytes());
        let old_lines = split_lines(old.as_bytes());
        let new_lines = split_lines(new.as_bytes());
        let mut prev = (0usize, 0usize);
        for (i, (a, b)) in m.iter().enumerate() {
            assert_eq!(old_lines[*a], new_lines[*b], "pair {i}");
            if i > 0 {
                assert!(*a > prev.0 && *b > prev.1, "monotonic at {i}");
            }
            prev = (*a, *b);
        }
    }
}
