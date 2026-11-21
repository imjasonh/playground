//! Runs the Sigstore conformance bundles through the device's checks.
//!
//! Each case's trusted root becomes a trust-root blob signed with the
//! development genesis keys, with the conformance beacon's identity as the
//! policy. A case whose directory ends in `_fail` must be rejected, either
//! while building the bundle container or by `c3_verify::sigstore::verify`.
//! Every other case must be accepted.

use std::fs;
use std::path::Path;

use c3_ota::blob::TrustRootSpec;
use c3_ota::blob::Window;
use c3_ota::blob::signed_blob;
use c3_ota::container::from_bundle_json;
use c3_ota::keys::read_signing_key;

const ROOT: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../testdata");

fn policy() -> [String; 5] {
    [
        "https://token.actions.githubusercontent.com".into(),
        "https://github.com/sigstore-conformance/extremely-dangerous-public-oidc-beacon/.github/workflows/extremely-dangerous-oidc-beacon.yml@refs/heads/main".into(),
        "632596897".into(),
        "131804563".into(),
        "workflow_dispatch".into(),
    ]
}

fn run_case(dir: &Path, digest: &[u8; 32]) -> Result<u64, String> {
    let bundle_json =
        fs::read_to_string(dir.join("bundle.sigstore.json")).map_err(|e| e.to_string())?;
    let root_json = fs::read_to_string(dir.join("trusted_root.json")).map_err(|e| e.to_string())?;
    let container = from_bundle_json(&bundle_json, None)?;
    let spec = TrustRootSpec::from_trusted_root(&root_json, 0, policy())?;
    let k1 = read_signing_key(&format!("{ROOT}/keys/genesis-dev-1.seed"))?;
    let k2 = read_signing_key(&format!("{ROOT}/keys/genesis-dev-2.seed"))?;
    let blob = signed_blob(&spec, &[(0, &k1), (1, &k2)])?;
    let root = c3_verify::trustroot::parse(&blob).map_err(|e| format!("blob: {e:?}"))?;
    let bundle = c3_verify::bundle::parse(&container).map_err(|e| format!("container: {e:?}"))?;
    let verified =
        c3_verify::sigstore::verify(&bundle, &root, digest).map_err(|e| format!("{e:?}"))?;
    Ok(verified.signed_time)
}

/// Cases whose timestamp authority has a P-256 key. The c3-boot profile
/// pins Sigstore's P-384 timestamp authority, so these are rejected no
/// matter what the suite expects.
const P256_TSA_CASES: [&str; 2] = [
    "rekor2-timestamp-outside-tsa-cert-validity_fail",
    "rekor2-timestamp-with-expired-cert-chain",
];

#[test]
fn conformance_cases() {
    let base = Path::new(ROOT).join("conformance");
    let digest = c3_crypto::sha256(&fs::read(base.join("a.txt")).unwrap());
    let mut dirs: Vec<_> = fs::read_dir(&base)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.is_dir())
        .collect();
    dirs.sort();
    assert!(dirs.len() >= 20, "expected the copied conformance cases");
    let mut failures = Vec::new();
    for dir in &dirs {
        let name = dir.file_name().unwrap().to_string_lossy().to_string();
        let result = run_case(dir, &digest);
        let should_fail = name.ends_with("_fail") || P256_TSA_CASES.contains(&name.as_str());
        match (&result, should_fail) {
            (Ok(_), false) | (Err(_), true) => {}
            _ => failures.push(format!("{name}: {result:?}")),
        }
        println!("{name}: {result:?}");
    }
    assert!(
        failures.is_empty(),
        "unexpected verdicts:\n{}",
        failures.join("\n")
    );
}

/// Verifies the happy-path bundle against a blob built from `spec`.
fn verify_with(spec: &TrustRootSpec) -> Result<u64, String> {
    let dir = Path::new(ROOT).join("conformance/rekor2-happy-path");
    let digest = c3_crypto::sha256(&fs::read(Path::new(ROOT).join("conformance/a.txt")).unwrap());
    let bundle_json = fs::read_to_string(dir.join("bundle.sigstore.json")).unwrap();
    let container = from_bundle_json(&bundle_json, None)?;
    let k1 = read_signing_key(&format!("{ROOT}/keys/genesis-dev-1.seed"))?;
    let k2 = read_signing_key(&format!("{ROOT}/keys/genesis-dev-2.seed"))?;
    let blob = signed_blob(spec, &[(0, &k1), (1, &k2)])?;
    let root = c3_verify::trustroot::parse(&blob).map_err(|e| format!("{e:?}"))?;
    let bundle = c3_verify::bundle::parse(&container).map_err(|e| format!("{e:?}"))?;
    c3_verify::sigstore::verify(&bundle, &root, &digest)
        .map(|v| v.signed_time)
        .map_err(|e| format!("{e:?}"))
}

#[test]
fn rejects_identity_and_window_changes() {
    let root_json =
        fs::read_to_string(Path::new(ROOT).join("conformance/rekor2-happy-path/trusted_root.json"))
            .unwrap();
    let base = TrustRootSpec::from_trusted_root(&root_json, 0, policy()).unwrap();
    let t = verify_with(&base).expect("the happy path verifies");

    for i in 0..5 {
        let mut longer = base.clone();
        longer.policy[i].push('x');
        assert_eq!(
            verify_with(&longer),
            Err("PolicyMismatch".into()),
            "policy {i} longer"
        );
        let mut shorter = base.clone();
        shorter.policy[i].pop();
        assert_eq!(
            verify_with(&shorter),
            Err("PolicyMismatch".into()),
            "policy {i} prefix"
        );
    }

    let moved: [fn(&mut TrustRootSpec, Window); 3] = [
        |s, w| s.fulcio.iter_mut().for_each(|e| e.2 = w),
        |s, w| s.logs.iter_mut().for_each(|e| e.2 = w),
        |s, w| s.tsas.iter_mut().for_each(|e| e.2 = w),
    ];
    for (i, set) in moved.iter().enumerate() {
        for w in [Window(0, t - 1), Window(t + 1, u64::MAX)] {
            let mut spec = base.clone();
            set(&mut spec, w);
            assert_eq!(
                verify_with(&spec),
                Err("OutsideWindow".into()),
                "window {i} {w:?}"
            );
        }
        let mut spec = base.clone();
        set(&mut spec, Window(t, t));
        assert_eq!(
            verify_with(&spec),
            Ok(t),
            "window {i} exactly at the signed time"
        );
    }
}
