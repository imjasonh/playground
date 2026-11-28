# Sigstore conformance fixtures

These bundles and trusted roots come from the
[sigstore-conformance](https://github.com/sigstore/sigstore-conformance)
test suite, `test/assets/bundle-verify/`, at commit
`006d1d9e395b3d8e840612eb846a54b33e36eac0`. sigstore-conformance is licensed
under the Apache License 2.0.

Only the Rekor v2 cases with a `messageSignature` are copied, because the
c3-boot profile accepts `hashedrekord` entries only. `a.txt` is the artifact
the happy-path bundles sign. A directory whose name ends in `_fail` holds a
bundle that a verifier must reject. The signing identity is the
sigstore-conformance OIDC beacon workflow, and the logs and timestamp
authority are Sigstore's staging instances.

Two cases use a local test timestamp authority with a P-256 key:
`rekor2-timestamp-outside-tsa-cert-validity_fail` and
`rekor2-timestamp-with-expired-cert-chain`. The c3-boot profile accepts only
Sigstore's P-384 timestamp authority, so both are rejected, and
`ota/tests/conformance.rs` expects that.
