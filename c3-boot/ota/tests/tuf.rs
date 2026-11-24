//! Checks every TUF case against its expected verdict, and checks that the
//! device reads the same keys from each trusted root as the host's blob
//! builder.

use c3_ota::blob::TrustRootSpec;
use c3_ota::tuf_cases::Input;
use c3_ota::tuf_cases::cases;

#[test]
fn cases_match_expectations() {
    let mut wrong = Vec::new();
    for case in cases() {
        let verdict = case.input.verdict();
        if let Some(expect) = case.expect
            && expect != verdict.starts_with("ok")
        {
            wrong.push(format!("{}: {verdict}", case.name));
        }
    }
    assert!(
        wrong.is_empty(),
        "unexpected verdicts:\n{}",
        wrong.join("\n")
    );
}

#[test]
fn real_chain_reaches_root_16() {
    let case = cases()
        .into_iter()
        .find(|c| c.name == "real_5_to_16")
        .expect("case exists");
    // Root 16 expires 2027-04-22T19:27:31Z, before targets 14.
    assert_eq!(case.input.verdict(), "ok 16 1808422051");
}

#[test]
fn device_reads_the_keys_the_blob_builder_reads() {
    let mut compared = 0;
    for case in cases() {
        let Input::Trusted { json } = &case.input else {
            continue;
        };
        if case.expect != Some(true) {
            continue;
        }
        // The blob builder rejects key types that the device skips.
        let Ok(spec) = TrustRootSpec::from_trusted_root(
            std::str::from_utf8(json).unwrap(),
            0,
            Default::default(),
        ) else {
            continue;
        };
        compared += 1;
        let mut buf = vec![0u8; c3_verify::trusted_root::buffer_len(json.len())];
        let policy = c3_verify::trustroot::Policy {
            issuer: b"",
            build_signer_uri: b"",
            repository_id: b"",
            owner_id: b"",
            trigger: b"",
        };
        let root = c3_verify::trusted_root::extract(json, policy, &mut buf).unwrap();
        let fulcio: Vec<_> = root
            .fulcio()
            .map(|f| {
                let w = f.window;
                (
                    f.subject.to_vec(),
                    *f.public_key,
                    (w.not_before, w.not_after),
                )
            })
            .collect();
        let expected: Vec<_> = spec
            .fulcio
            .iter()
            .map(|(s, k, w)| (s.clone(), *k, (w.0, w.1)))
            .collect();
        assert_eq!(fulcio, expected, "{} fulcio", case.name);
        let logs: Vec<_> = root
            .logs()
            .map(|l| {
                let w = l.window;
                (
                    l.origin.to_vec(),
                    *l.public_key,
                    (w.not_before, w.not_after),
                )
            })
            .collect();
        let expected: Vec<_> = spec
            .logs
            .iter()
            .map(|(o, k, w)| (o.as_bytes().to_vec(), *k, (w.0, w.1)))
            .collect();
        assert_eq!(logs, expected, "{} logs", case.name);
        let tsas: Vec<_> = root
            .tsas()
            .map(|t| {
                let w = t.window;
                (
                    t.signer_id.to_vec(),
                    *t.public_key,
                    (w.not_before, w.not_after),
                )
            })
            .collect();
        let expected: Vec<_> = spec
            .tsas
            .iter()
            .map(|(s, k, w)| (s.clone(), *k, (w.0, w.1)))
            .collect();
        assert_eq!(tsas, expected, "{} tsas", case.name);
    }
    assert!(compared >= 2, "compared {compared} trusted roots");
}
