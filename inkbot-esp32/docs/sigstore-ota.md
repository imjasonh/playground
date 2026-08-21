# Sigstore OTA for inkbot-esp32

## Goal

Sign firmware with **Sigstore keyless** (GitHub Actions OIDC → Fulcio → Rekor)
and refuse to install an OTA image that does not verify as that identity.

## Can the ESP-IDF bootloader do this?

**Not as a fork that embeds full Sigstore.** Keep the stock second-stage
bootloader.

| Constraint | Why it blocks Sigstore in the bootloader |
|------------|------------------------------------------|
| Size | Default room is **28 KiB** (`0x1000`…`0x8000`). Secure Boot V2 caps the bootloader around **48 KiB**. A Cosign/Fulcio/Rekor verifier is far larger. |
| Job of the bootloader | It **selects** an OTA slot and loads the app. It does **not** download images. `esp_https_ota` runs in the application. |
| Stack | Custom `bootloader_components` are freestanding C with a tiny API surface. `sigstore-verify` and friends need alloc, X.509, JSON, and trust roots. |
| Rust second stage | Espressif’s Rust-on-ESP book still treats the **ESP-IDF bootloader** as the supported second stage. `esp-bootloader-esp-idf` is an *app* helper, not a replacement bootloader. |

ESP Secure Boot (eFuse keys + `espsecure`) is a different trust system. It can
sit beside Sigstore; it does not consume Cosign bundles or GitHub OIDC
identities.

## Where Sigstore belongs

```
CI (main)          Worker / R2              Device app
─────────          ───────────              ──────────
build app.bin  →   store bin + bundle  →    HTTPS GET
cosign sign-blob                            SHA-256 + offline verify
  (GH OIDC)                                 only then esp_ota_set_boot
verify-blob gate                            reboot → mark valid / rollback
```

Security property: **the update channel** only accepts images signed by the
pinned workflow identity. A compromised app could skip the gate; stopping that
needs Secure Boot / a measured boot path, not a bigger Sigstore bootloader.

## Identity pin

Verify both with **exact** strings (no regexp):

- OIDC issuer: `https://token.actions.githubusercontent.com`
- Certificate identity:
  `https://github.com/imjasonh/playground/.github/workflows/inkbot-esp32.yml@refs/heads/main`

Cosign: `--certificate-identity` and `--certificate-oidc-issuer`. The same
literals live in [`src/sigstore_ota.rs`](../src/sigstore_ota.rs) as
`DEFAULT_CERTIFICATE_IDENTITY` / `GITHUB_ACTIONS_OIDC_ISSUER`.

## Repo pieces

| Piece | Role |
|-------|------|
| [`src/sigstore_ota.rs`](../src/sigstore_ota.rs) | Host-tested policy, digest binding, Cosign CLI verify helper |
| This doc | Architecture and non-goals |
| `inkbot-esp32.yml` (on `main`) | Keyless `sign-blob` + `verify-blob` on the built ELF |

Device-side verify (mbedtls / slim Rust on esp-idf) and A/B partitions are the
next steps after the CI provenance path is green. Do not grow the IDF
bootloader for Fulcio/Rekor.

## Non-goals

- Forking or replacing the ESP-IDF second-stage bootloader with Sigstore
- On-device TUF refresh of Sigstore roots in v1
- Signing the maze binary for OTA (USB-only demo image)
