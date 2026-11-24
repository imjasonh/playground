//! Fuzzes the TUF checks behind `c3-verify`'s `tuf` feature. If the first
//! byte is 0, the rest is a JSON document, parsed in both profiles and
//! walked. Otherwise the rest is a TUF part, checked from Sigstore's root 5,
//! and its `trusted_root.json` is read whether or not that check passes.

#![no_main]

use c3_verify::json::Mode;
use c3_verify::json::Value;
use c3_verify::trustroot::Policy;
use libfuzzer_sys::fuzz_target;

const PINNED: &[u8] = include_bytes!("../../testdata/tuf/5.root.json");

const POLICY: Policy<'static> = Policy {
    issuer: b"https://token.actions.githubusercontent.com",
    build_signer_uri: b"https://github.com/imjasonh/playground/.github/workflows/c3-release.yml@refs/heads/main",
    repository_id: b"1234",
    owner_id: b"5678",
    trigger: b"push",
};

fn walk(v: Value<'_>, depth: usize) {
    if depth > c3_verify::json::MAX_DEPTH {
        return;
    }
    let _ = (v.str(), v.u64());
    if let Ok(mut members) = v.members() {
        while let Ok(Some((key, value))) = members.next_member() {
            let _ = v.get(key);
            walk(value, depth + 1);
        }
    }
    if let Ok(mut elements) = v.elements() {
        while let Ok(Some(value)) = elements.next_element() {
            walk(value, depth + 1);
        }
    }
}

fuzz_target!(|data: &[u8]| {
    let Some((&kind, rest)) = data.split_first() else {
        return;
    };
    if kind == 0 {
        for mode in [Mode::Strict, Mode::Canonical] {
            if let Ok(v) = c3_verify::json::parse(rest, mode) {
                walk(v, 0);
            }
        }
        return;
    }
    let Ok(len) = u32::try_from(rest.len()) else {
        return;
    };
    let Ok(index) = c3_verify::tuf::read_index(&mut &rest[..], len) else {
        return;
    };
    let mut doc = vec![0u8; c3_verify::tuf::MAX_DOC_LEN as usize];
    let _ = c3_verify::tuf::verify(PINNED, &mut &rest[..], len, &mut doc);
    let Ok((offset, len)) = index.doc(index.roots() + 1) else {
        return;
    };
    let Some(trusted_root) = rest.get(offset as usize..(offset + len) as usize) else {
        return;
    };
    let mut buf = vec![0u8; c3_verify::trusted_root::buffer_len(trusted_root.len())];
    let _ = c3_verify::trusted_root::extract(trusted_root, POLICY, &mut buf);
});
