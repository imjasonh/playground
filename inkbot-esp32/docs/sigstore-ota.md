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
cosign sign-blob                            read pins from NVS
  (GH OIDC)                                 SHA-256 + offline verify
verify-blob gate                            only then esp_ota_set_boot
                                            reboot → mark valid / rollback
```

Security property: **the update channel** only accepts images signed by the
identity pinned **on the device** at flash/provision time. The ELF does not
contain a repo or workflow string.

## Identity pin (flash-time NVS)

Exact strings only (no regexp), stored under NVS namespace `sigstore`:

| Key | Meaning | Example |
|-----|---------|---------|
| `oidc_iss` | Fulcio OIDC issuer | `https://token.actions.githubusercontent.com` |
| `cert_id` | Fulcio cert identity (SAN URI) | `https://github.com/<owner>/<repo>/.github/workflows/inkbot-esp32.yml@refs/heads/main` |

Provision without rebuilding:

```bash
cp nvs/sigstore.csv.example nvs/sigstore.csv
# edit cert_id
make nvs-sigstore PORT=/dev/cu.usbserial-XXXX
```

`make nvs-sigstore` runs ESP-IDF’s `nvs_partition_gen.py` and writes the blob
at the default NVS offset (`0x9000` on the stock table). Missing keys mean
Sigstore OTA verify stays disabled until you provision.

CI still passes `--certificate-identity` into Cosign when **signing** artifacts;
that is workflow config, not firmware.

## Repo pieces

| Piece | Role |
|-------|------|
| [`src/sigstore_ota.rs`](../src/sigstore_ota.rs) | Policy from NVS strings, digest binding, Cosign CLI helper |
| [`nvs/sigstore.csv.example`](../nvs/sigstore.csv.example) | Flash-time pin template |
| This doc | Architecture and non-goals |
| `inkbot-esp32.yml` (on `main`) | Keyless `sign-blob` + `verify-blob` on the built ELF |

Device-side verify (mbedtls / slim Rust on esp-idf) and A/B partitions are the
next steps after the CI provenance path is green. Do not grow the IDF
bootloader for Fulcio/Rekor.

## Non-goals

- Forking or replacing the ESP-IDF second-stage bootloader with Sigstore
- Compiling issuer/identity into the firmware binary
- On-device TUF refresh of Sigstore roots in v1
- Signing the maze binary for OTA (USB-only demo image)
