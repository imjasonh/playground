# Development keys

These keys sign the development TUF repository, which stands in for
Sigstore's in tests and QEMU runs. Their seeds are public, so anyone can
sign metadata that a development bootloader accepts. Never flash a
development bootloader to a real device. The bootloader build requires
`C3_TUF_ROOT`: set it to a canonical Sigstore root, or to `dev` to pin
`tuf-dev-root.json`. A `dev` build prints a warning on every boot.

- `tuf-dev-root-1.seed` through `tuf-dev-root-3.seed`: hex-encoded P-256
  scalars of the root keys.
- `tuf-dev-targets-1.seed` and `tuf-dev-targets-2.seed`: hex-encoded P-256
  scalars of the targets keys. Root version 1 trusts the first, and root
  version 2 rotates to the second.
- `tuf-dev-root.json`: root version 1, in canonical JSON. Regenerate it
  with `c3-ota tuf-dev-root --keys testdata/keys --version 1 --out
  testdata/keys/tuf-dev-root.json`. A test fails when it is out of date.
- `dev-policy`: the release identity that fakestore puts in its
  certificates, which development bootloaders compile in.
