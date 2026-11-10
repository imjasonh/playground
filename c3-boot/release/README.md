# c3-boot releases

`.github/workflows/c3-release.yml` signs the demo application with
production Sigstore and checks the result the way a device would. It has
three jobs:

1. **Build** packs the demo application into a c3-boot image. It has no OIDC
   token.
1. **Sign** runs `cosign sign-blob` with the files in this directory, then
   `cosign verify-blob` against the run's own identity. It is the only job
   that asks for `id-token: write`, and it runs no repository code, because
   any step in it could sign arbitrary bytes as the workflow.
1. **Check** runs [`check.sh`](check.sh): it converts the bundle, builds a
   trust-root blob that pins the signer's identity, assembles a slot, runs
   the device's checks on the host, and boots the slot in Espressif's QEMU.

Same-repository pull requests sign too, so changes get tested against
production Sigstore before they merge. A pull request runs its own copy of
the workflow and pinned files, so it can sign anything, as anyone who can
push a branch can with any workflow. Its certificate names the
`refs/pull/N/merge` ref and the `pull_request` trigger, though, and the
production identity policy pins `refs/heads/main` and `push`, which only a
merge to the protected `main` branch produces. A pull request's signature
never satisfies a production trust root.

The check job's blob and bootloader use the public development genesis
keys, so its slot is for tests only. A production trust-root blob is signed
offline, as the plan's rotation process describes.

## Pinned files

- `trusted_root.json` is Sigstore's production trusted root, copied from
  [`sigstore/root-signing`](https://github.com/sigstore/root-signing) at
  commit `f22ebe7cea5352c2c3b675aa211f730e279c7b78`
  (`targets/trusted_root.json`, SHA-256
  `6494e21ea73fa7ee769f85f57d5a3e6a08725eae1e38c755fc3517c9e6bc0b66`).
- `signing_config.json` is Sigstore's production signing configuration
  (`targets/signing_config_rekor_v2.v0.2.json` at the same commit) with the
  Rekor v1 log removed. With both logs listed, cosign may pick either, and
  c3-boot accepts only Rekor v2 entries.

To update them, copy the new files from `sigstore/root-signing`, remove any
Rekor v1 log from the signing configuration, and update the commit and hash
above. The plan's `c3-trust-root.yml` job will automate this.

## Check a release locally

To check an image and bundle without production Sigstore, sign the image
with [fakestore](../fakestore/README.md) and pass fakestore's identity:

```bash
C3_ISSUER=https://token.actions.githubusercontent.com \
C3_BUILD_SIGNER_URI=https://github.com/imjasonh/playground/.github/workflows/c3-release.yml@refs/heads/main \
C3_REPOSITORY_ID=1234 C3_OWNER_ID=5678 C3_TRIGGER=push \
  bash release/check.sh IMAGE BUNDLE TRUSTED_ROOT WORK_DIR
```

Replace `IMAGE` with the packed image, `BUNDLE` with the Sigstore bundle,
`TRUSTED_ROOT` with fakestore's `trusted_root.json`, and `WORK_DIR` with a
directory for the output.
