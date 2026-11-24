# c3-boot releases

`.github/workflows/c3-release.yml` signs the demo application with
production Sigstore and checks the result the way a device would. It has
three jobs:

1. **Build** packs the demo application into a c3-boot image, and packages
   the slot's TUF part with [`package-tuf.sh`](package-tuf.sh): each
   Sigstore root in `../testdata/tuf/` newer than `pinned-root.json`, then
   `targets.json` and `trusted_root.json`. It checks that part from the
   pinned root with the device's code before anything is signed. It has no
   OIDC token.
1. **Sign** runs `cosign sign-blob` with the files in this directory, then
   `cosign verify-blob` against the run's own identity. It is the only job
   that asks for `id-token: write`, and it runs no repository code, because
   any step in it could sign arbitrary bytes as the workflow.
1. **Check** runs [`check.sh`](check.sh): it converts the bundle, assembles
   a slot with the TUF part, runs the device's checks on the host, and boots
   the slot in Espressif's QEMU with a bootloader that pins
   `pinned-root.json` and the identity of the run that signed.

Same-repository pull requests sign too, so changes get tested against
production Sigstore before they merge. A pull request runs its own copy of
the workflow and pinned files, so it can sign anything, as anyone who can
push a branch can with any workflow. Its certificate names the
`refs/pull/N/merge` ref and the `pull_request` trigger, though, and the
production identity policy pins `refs/heads/main` and `push`, which only a
merge to the protected `main` branch produces. A pull request's signature
never satisfies the policy that a production bootloader compiles in.

## Pinned files

- `pinned-root.json` is Sigstore's TUF root version 16
  (`../testdata/tuf/16.root.json`) in canonical form, as
  `c3-ota tuf-root` writes it. Production bootloaders compile it in.
- `policy` is the release identity that production bootloaders compile
  in: `c3-release.yml` on `refs/heads/main`, run by a push to this
  repository.
- `trusted_root.json` is Sigstore's production trusted root, copied from
  [`sigstore/root-signing`](https://github.com/sigstore/root-signing) at
  commit `f22ebe7cea5352c2c3b675aa211f730e279c7b78`
  (`targets/trusted_root.json`, SHA-256
  `6494e21ea73fa7ee769f85f57d5a3e6a08725eae1e38c755fc3517c9e6bc0b66`).
- `signing_config.json` is Sigstore's production signing configuration
  (`targets/signing_config_rekor_v2.v0.2.json` at the same commit) with the
  Rekor v1 log removed. With both logs listed, cosign may pick either, and
  c3-boot accepts only Rekor v2 entries.

`.github/workflows/c3-trust-root.yml` checks `sigstore/root-signing` every
Monday with `.github/scripts/update-c3-trust-root.sh`. When the TUF
metadata or either file changes, it refreshes `../testdata/tuf/`, updates
both files, drops any log but Rekor v2 from the signing configuration,
updates the commit and hash above, and opens a pull request that shows the
TUF check from `pinned-root.json` (`c3-ota tuf-verify`) and the entries the
device would read from the new trusted root (`c3-ota describe`). Devices
follow a new Sigstore root through the TUF part of the next release, so
`pinned-root.json` changes only with a bootloader reflash over USB. To test
the script, run `bash .github/scripts/update-c3-trust-root_test.sh`.

## Check a release locally

To check an image and bundle without production Sigstore, sign the image
with [fakestore](../fakestore/README.md), package a TUF part from the
development repository over fakestore's trusted root, and pass fakestore's
identity:

```bash
cargo run -q -p c3-ota -- tuf-dev-targets --keys testdata/keys --root-version 1 \
  --trusted-root FAKESTORE_ROOT --out targets.json
cargo run -q -p c3-ota -- tuf-package --targets targets.json \
  --trusted-root FAKESTORE_ROOT --out tuf.bin
C3_TUF_ROOT=dev \
C3_ISSUER=https://token.actions.githubusercontent.com \
C3_BUILD_SIGNER_URI=https://github.com/imjasonh/playground/.github/workflows/c3-release.yml@refs/heads/main \
C3_REPOSITORY_ID=1234 C3_OWNER_ID=5678 C3_TRIGGER=push \
  bash release/check.sh IMAGE BUNDLE tuf.bin WORK_DIR
```

Replace `FAKESTORE_ROOT` with fakestore's `trusted_root.json`, `IMAGE` with
the packed image, `BUNDLE` with the Sigstore bundle, and `WORK_DIR` with a
directory for the output.
