# OTA updates over GHCR with cosign verification

This document describes how OTA updates work end-to-end: how firmware
is built and signed in CI, how it's distributed via an OCI registry,
how the device discovers and applies updates, how per-device config
gets onto the device in the first place, and how the device protects
against bad updates and unauthorized signers.

## Architecture

```
                                                  GitHub
                                                Container
                                                Registry
                                                  (GHCR)
   developer push                                    │
   ──────────────▶  ┌──────────────────┐ push       ▼            poll
                    │  GHA workflow    │ ─────▶ ┌────────┐ ◀────────────
                    │esp32-publish.yml │ sign   │  OCI   │   pull bundle
                    │   • cargo build  │ ─────▶ │artifact│   verify sig
                    │   • espflash     │        │ + sig  │   stream blob
                    │   • OCI push     │        └────────┘   write OTA
                    │   • cosign sign  │                     reboot
                    │     (keyless,    │                       │
                    │      OIDC)       │                       ▼
                    └──────────────────┘                   ┌────────┐
                                                           │ ESP32  │
                                                           └────────┘
```

The published OCI artifact contains **only firmware code** — no Wi-Fi
creds, no trust roots, no per-device config. Same bytes can run on any
device. Per-device data lives in the device's NVS partition and is
written via USB at provisioning time (see [Provisioning](#provisioning)).

Manual `make publish` from a developer machine works the same way as
the GHA workflow — just cosigns with a different OIDC identity (a
developer's email instead of the workflow's URI).

## Components

| Component | Lives at | Role |
|---|---|---|
| **Publisher** | `tools/publisher/` (Rust, host build) | Wraps the firmware `.bin` as an OCI artifact and pushes both `:latest` and `:sha-<short>` tags to GHCR. Prints the manifest digest on stdout for the next step. |
| **Provisioner** | `tools/provision/` (Rust, host build) | Reads `provisioning.toml`, builds an NVS partition image via ESP-IDF's `nvs_partition_gen.py`, flashes it to the device over USB. |
| **Cosign** | system binary, version 3 | Signs the just-pushed digest using keyless OIDC. Stores the signature as a sibling OCI artifact (Sigstore Bundle v0.3 format). |
| **GHA publish workflow** | `../.github/workflows/esp32-publish.yml` | Runs `make APP=eink publish` on relevant pushes to main. Uses ambient OIDC token for cosign — no secrets needed for signing. Only the auto-injected `GITHUB_TOKEN` is required. |
| **CI workflow** | `../.github/workflows/esp32.yml` | Runs host tests and cross-builds both firmware applications on PRs. No publishing or signing. |
| **OTA loop** | `src/ota.rs` | Background pthread, polls GHCR every 60 s with backoff + jitter, fetches manifest, compares to last applied. |
| **Sig verifier** | `src/sig.rs` | Parses Sigstore Bundle v0.3, verifies cert chain + DSSE signature + in-toto subject digest. |
| **Trust loader** | `src/trust.rs` | Reads the allowlist of `(identity, issuer)` pairs and bundled Sigstore Fulcio root + intermediate CAs from NVS at boot. |

## Partition layout (4 MB flash)

```
0x001000  bootloader             (~28 KB)
0x008000  partition table          4 KB
0x009000  nvs                     24 KB    OTA state + provisioned per-device config
0x00f000  otadata                  8 KB    which slot to boot
0x011000  phy_init                 4 KB
0x020000  ota_0                  1.94 MB   app slot 0
0x210000  ota_1                  1.94 MB   app slot 1
```

The two app slots ping-pong: a new image always writes to the *inactive*
slot, then `otadata` is updated to point at it on next boot.

`partitions.csv` is the source of truth. The Makefile substitutes the
absolute project path into `sdkconfig.defaults.in` because IDF resolves
`CONFIG_PARTITION_TABLE_CUSTOM_FILENAME` relative to embuild's synthetic
project under `target/`, not the repo root.

## NVS schema

Per-device config and runtime OTA state live in NVS, organized by
namespace. `tools/provision/` writes the config; the firmware reads at
boot.

```
ns      key             type   notes
─────────────────────────────────────────────────────────────────────
wifi    ssid            str    network SSID (provisioned)
wifi    pass            str    PSK (provisioned)

ssh     host            str    target SSH hostname (provisioned)
ssh     port            u16    target port, normally 22 (provisioned)
ssh     username        str    remote account (provisioned)
ssh     host_key        blob   pinned 32-byte Ed25519 server key (provisioned)
ssh     command         str    command executed by the read-only client (provisioned)
ssh     client_seed     blob   generated 32-byte Ed25519 seed (runtime, e-ink)

ota     last_digest     str    last successfully-applied layer digest (runtime)
ota     pending_digest  str    set during update, promoted on mark-valid (runtime)
ota     repo            str    optional override of compile-time default
ota     tag             str    optional override (default "latest")
ota     poll_secs       u32    optional override (default 60)

trust   identities      blob   JSON: [{"identity":"...","issuer":"..."}, ...]
trust   fulcio_root     blob   PEM bytes (Sigstore root CA)
trust   fulcio_inter    blob   PEM bytes (Sigstore intermediate CA)

gcp     project_id      str    optional; cloud-logging GCP project
gcp     sa_email        str    optional; logging service-account email
gcp     sa_key_id       str    optional; key id for the JWT `kid` header
gcp     sa_key_pem      blob   optional; RSA private key PKCS#8 PEM
gcp     min_severity    u8     optional; 0=TRACE..4=ERROR (default 2=INFO)
```

The `gcp` namespace is opt-in. If any required key is missing, the
device boots with serial-only logging and never talks to GCP. See
[`observability.md`](observability.md).

The `wifi` and `trust` namespaces are written by `make provision` and
never touched by OTA. The `ota` namespace is written at runtime by the
firmware's OTA loop.

## Provisioning

### `provisioning.toml`

The single source of truth for per-device config. Gitignored. Copy from
`provisioning.toml.example`, fill in:

```toml
[wifi]
ssid = "..."
pass = "..."

[trust]
fulcio_root_pem = "trust/fulcio_root.pem"
fulcio_intermediate_pem = "trust/fulcio_intermediate.pem"

[[trust.identities]]
identity = "https://github.com/imjasonh/playground/.github/workflows/esp32-publish.yml@refs/heads/main"
issuer = "https://token.actions.githubusercontent.com"
```

Add a developer email/issuer identity only when manual publishing is required;
the main-branch workflow is the least-privilege default.
Rekor shard keys and TSA certificates are public, versioned firmware inputs
under `trust/`, sourced from Sigstore's TUF targets. A transition firmware keeps
old and new shard keys together and is published while the old shard still
accepts entries, allowing the signed OTA itself to rotate public trust without
USB access.

Lose this file = lose your secrets. Keep a copy in a password manager.

### `tools/provision/` flow

1. Reads `provisioning.toml`.
2. Generates an intermediate CSV in the format ESP-IDF's
   `nvs_partition_gen.py` expects (one row per key, `binary` rows
   reference files on disk).
3. Shells out to `nvs_partition_gen.py` (in `.embuild/`, present after
   `make build` has run once) to produce a 24 KB NVS partition image.
4. Optionally `espflash write-bin --address 0x9000 target/nvs.bin` to
   write it to the device.

### Bootstrapping a new device

```
make provisioning.toml             # creates from template (one-time)
$EDITOR provisioning.toml          # fill in wifi creds + trust identities
make bootstrap                     # build, flash everything, write NVS
make monitor                       # watch it boot and connect
```

`make bootstrap` is `flash-all` + `provision`. After it completes the
device boots, reads NVS for wifi + trust, connects to Wi-Fi, starts
polling GHCR. From then on updates flow over OTA.

### Strict-inert when not provisioned

If a device boots and any of the required NVS keys (`wifi/ssid`,
`wifi/pass`, `trust/identities`, `trust/fulcio_root`,
`trust/fulcio_inter`) is missing, the firmware logs
`NOT PROVISIONED — run \`make provision\`` to serial every 30 seconds
and refuses to start Wi-Fi or OTA. No surprise boots, no fallback
creds. Run `make provision` to fix.

## Update mechanism

### Polling loop (firmware, `src/ota.rs::run`)

1. Sleep `poll_interval ± 10%` jitter (default 60 s, NVS-configurable
   via `ota/poll_secs`).
2. Hit GHCR's anonymous token endpoint with scope
   `repository:<repo>:pull`, get a Bearer token.
3. `GET /v2/<repo>/manifests/<tag>` with that token. Compute SHA-256
   of the response body — that's the manifest digest cosign signed.
4. Parse manifest. Require exactly one
   `application/vnd.esp32.firmware.bin` layer, a valid SHA-256 descriptor,
   and a nonzero size no larger than ESP-IDF's inactive OTA partition.
   Compare its digest to `last_digest` from NVS.
   - Match → `NoChange`, return to (1).
   - Different → continue.
5. **Verify the signature** (see [Device verification](#device-verification-srcsigrs)
   below). On failure → log, increment `consecutive_failures`, return
   to (1) with exponential backoff (`60 s × 2^failures`, capped at 1 h).
6. Fetch and digest-check the signed manifest's small config blob. Require its
   `app_id`, `target_chip`, binary size, and binary SHA to match this firmware
   and its layer descriptor.
7. `GET /v2/<repo>/blobs/<layer-digest>`. Stream the body chunk by
   chunk into the inactive OTA partition via `EspOta::write()`,
   updating an SHA-256 hasher in parallel.
8. After last byte: confirm `(actual size, actual SHA)` matches the
   manifest descriptor. On any mismatch → `EspOta::abort()`, fail
   loudly. On match → `EspOta::complete()` (sets boot partition).
9. Persist `pending_digest = layer.digest` to NVS.
10. `esp_restart()`.

### Post-reboot validation (firmware, `src/main.rs`)

1. Early in `main()`, call `is_pending_verify()` →
   reads `esp_ota_get_state_partition()`.
2. If `ESP_OTA_IMG_PENDING_VERIFY`, run the application bringup checks. Both
   applications connect Wi-Fi; e-ink additionally completes a full panel
   refresh. OTA verification itself needs no current clock.
3. On bringup success, call
   `esp_ota_mark_app_valid_cancel_rollback()` and promote
   `pending_digest → last_digest` in NVS.
4. On failure, `esp_restart()` — the bootloader rolls back to the
   previous slot on the next boot because the new image was never
   marked valid.
5. Spawn the OTA polling thread with a 48 KB stack (HTTPS + JSON +
   SHA + cert parsing + ECDSA needs the headroom).

## Anti-bricking + USB recovery

Two layers of protection:

### Layer 1 — bootloader rollback (always armed in firmware)

`CONFIG_BOOTLOADER_APP_ROLLBACK_ENABLE=y` in `sdkconfig.defaults.in`
turns on ESP-IDF's pending-verify state. After an OTA reboot, the new
app runs in `PENDING_VERIFY`. If `mark_app_valid` isn't called before
the next reboot, the bootloader reverts. We gate `mark_app_valid` on
networking actually working — so an OTA that breaks Wi-Fi or DNS or
TLS auto-rolls back.

### Layer 2 — USB recovery (when both slots are bad)

If both OTA slots end up unbootable, or the bootloader / partition
table itself is corrupted, recover over USB:

1. Put the chip in serial download mode. The Inland board has
   auto-reset; espflash usually drives DTR/RTS automatically. If
   not: hold **BOOT** (IO0), tap **EN**, release BOOT.
2. From the project root:
   ```
   make bootstrap   # full flash + re-provision
   # or:
   make flash-all   # full flash without re-provisioning (NVS preserved
                    # only if not previously erased)
   ```

`make bootstrap` wipes flash entirely and writes everything back
including NVS, so it's the most reliable recovery path. Brief downtime;
no risk of brick.

## CI signing (publisher → GHCR)

### Publisher tool

`tools/publisher/` is a separate cargo project (its own
`rust-toolchain.toml` pinning `stable`, its own `.cargo/config.toml`
clearing the parent's xtensa target). Built for the host.

CLI:

```
publisher push --bin <fw.bin> --repo ghcr.io/<owner>/<name> \
  --app-id <blinky|eink> --git-sha <short>
```

Produces an OCI manifest with:

- **Config**: `application/vnd.esp32.firmware.v1+json` — small JSON
  with `app_id`, `target_chip`, `idf_version`, `git_sha`, `built_at`,
  `bin_size`, `bin_sha256`.
- **Layer**: `application/vnd.esp32.firmware.bin` — the raw firmware
  bytes (no compression).
- **Annotations**: `org.opencontainers.image.source` so GHCR auto-links
  the package to the source repo on first push;
  `org.opencontainers.image.revision`, `created`.

Pushes the same artifact under both `:latest` and `:sha-<short>`. Both
tags resolve to the same content-addressed digest, so one cosign sign
covers both.

The publisher prints `digest: sha256:...` on stdout. The Makefile
captures it and passes it to `cosign sign` as `<repo>@<digest>` rather
than a tag — eliminates the race window between publisher push and
cosign sign.

### Cosign signing

`make publish` runs `cosign sign --yes <repo>@<digest>` after the
publisher push. Cosign:

1. Authenticates to its OIDC issuer (Sigstore's broker for interactive
   browser flow; or the workflow's ambient ID token in GHA).
2. Fetches a short-lived (10 min) X.509 cert from Fulcio with the
   OIDC identity baked in as a SAN.
3. Hashes the manifest payload, signs it with the cert's private key.
4. Bundles cert + signature + (optional) Rekor entry into a Sigstore
   Bundle v0.3 (Protobuf-as-JSON).
5. Pushes the bundle as a sibling OCI artifact at tag
   `sha256-<hex>` (no `.sig` suffix) using the OCI 1.1 referrers
   layout (image index → inner manifest → bundle blob).

### Identities used

| Source | OIDC issuer | SAN form |
|---|---|---|
| Manual `make publish` | `https://accounts.google.com` | `rfc822Name` (developer's email) |
| GHA workflow on push to main | `https://token.actions.githubusercontent.com` | `URI` (`https://github.com/imjasonh/playground/.github/workflows/esp32-publish.yml@refs/heads/main`) |

Only identities explicitly present in `trust/identities` (NVS) are accepted.
The template trusts the GHA workflow only; add the manual identity only when
needed. Updating the allowlist requires editing `provisioning.toml` and
re-running `make provision`; OTA cannot grant new signing identities.

### GHA workflow specifics

- Trigger: `push` to `main`, plus `workflow_dispatch` for manual
  reruns.
- Concurrency: `cancel-in-progress: true` with a single group, so a
  rapid sequence of pushes only publishes the latest commit.
- Permissions: `packages: write` (push to GHCR), `id-token: write`
  (cosign keyless OIDC), `contents: read`.
- Uses `astral-sh/setup-uv@v7` to provide Python 3.12 (the Makefile's
  `ensure-python-shim` symlinks `python3` to it),
  `esp-rs/xtensa-toolchain@v1.7` for the Xtensa Rust toolchain,
  `sigstore/cosign-installer@v4.1.1` for cosign 3.
- Only secret needed: the auto-injected `GITHUB_TOKEN` (gets written
  to `gh.env` for cosign's registry auth). Wi-Fi creds and trust
  config are not in the firmware image and therefore not in the build.

## Device verification (`src/sig.rs`)

For each candidate update, before downloading the firmware blob:

1. **Fetch the bundle.** Walk the OCI 1.1 referrers layout: image
   index at tag `sha256-<manifest-digest>` → inner manifest →
   `application/vnd.dev.sigstore.bundle.v0.3+json` layer blob.
2. **Parse the leaf cert.** Decode `verificationMaterial.certificate.
   rawBytes` from base64, parse as DER X.509 with the `x509-cert`
   crate.
3. **Identity check.** Read SAN extension. Accept either
   `Rfc822Name` (email) or `UniformResourceIdentifier` (workflow
   URI). Read OIDC issuer from extension OID
   `1.3.6.1.4.1.57264.1.1`. Reject if `(identity, issuer)` isn't in
   `trust/identities` (loaded from NVS at boot).
4. **Offline transparency verification.** Select a versioned Rekor shard key by
   full log ID. For v1, verify the SET, P-256 checkpoint, integrated time, and
   inclusion proof. For v2, verify the hashedrekord DSSE binding, Ed25519
   checkpoint, inclusion proof, and RFC3161 TSA timestamp. No Rekor network
   request is made.
5. **Cert chain and signing time.** Verify leaf was signed by the provisioned
   Sigstore intermediate (P-384 ECDSA-SHA384). Verify intermediate was signed
   by the provisioned Sigstore root (also P-384 ECDSA-SHA384). Both are loaded
   from NVS (`trust/fulcio_inter`, `trust/fulcio_root`). Require every
   certificate to be valid at Rekor v1's integrated time or the v2 TSA time,
   not at the device's current time.
6. **DSSE signature.** Decode `dsseEnvelope.payload` (base64) and
   `signatures[0].sig` (base64). Compute the DSSE PAE
   (`"DSSEv1 <len> <payloadType> <len> <payload>"`). Verify the
   ECDSA-P256 signature using the leaf cert's public key.
7. **In-toto binding.** Parse the DSSE payload as an in-toto
   Statement. Confirm `subject[0].digest.sha256` exactly matches the
   manifest digest we're about to install. This is the cryptographic
   binding from "what the signer attested" to "what we're about to
   apply".

If any step fails, the verifier returns an error. The OTA loop logs
it (with anyhow chain), bumps `consecutive_failures` (driving
backoff), and never touches the OTA partition.

### Rekor v2 shard rotation

Sigstore v2 shards approximately every six months. Before signing switches,
update the committed `trust/rekor-v2.pub` and
`trust/signing-config-rekor-v2.json` in a normal reviewed release while the
previous shard still accepts entries. Keep previous verification keys in the
firmware keyring so old bundles remain verifiable. A device that misses the
entire overlap may still require USB recovery; rotation therefore depends on
Sigstore's announced overlap window, not an online Rekor lookup at OTA time.

## Trust separation: soft vs hard

Per-device signer identities and Fulcio CAs live in NVS. Public Rekor shard
keys and TSA certificates are versioned with firmware so overlapping shards
can rotate through OTA.

But it's a **soft guarantee**. The OTA-distributed firmware code is
what reads NVS and runs the verifier; a malicious image could ignore
NVS and hardcode "trust everyone". To prevent that cryptographically,
we'd need **Secure Boot v2** (RSA-3072 keypair, public-key digest
burned into eFuses, bootloader cryptographically verifies the app
before running) plus **Flash Encryption** (also eFuse-rooted) so an
attacker with physical access can't dump flash to extract the secrets
that NVS holds. Both are irreversible eFuse burns; significant effort
and risk; massive security upgrade. See [Future work](#future-work).

In practice the soft guarantee is enough here:

- The OCI image is no longer a per-device artifact — same bytes
  everywhere, no embedded secrets.
- Trust changes happen via a deliberate USB re-provision, not as a
  side effect of regular OTA.
- The convention is enforced by code review of the firmware that
  gets signed and shipped.

## Future work

- **GitHub Actions OIDC trust scoping by `job_workflow_ref`.** The
  GHA identity in `trust/identities` pins to
  `esp32-publish.yml@refs/heads/main`. We could also enforce
  `1.3.6.1.4.1.57264.1.x` Fulcio extensions like `Run Invocation
  URI` for stricter trust.
- **Force-update GPIO button.** Wire a button to a GPIO; on short
  press, skip the poll wait and trigger an immediate poll.
- **Auto-reboot on bringup failure.** If `connect_wifi` errors during
  PENDING_VERIFY, currently `main` exits with the error and IDF
  doesn't auto-reboot — the user has to power-cycle to trigger the
  bootloader rollback. Cleaner: explicit `esp_restart()` so rollback
  happens automatically.
- **`If-None-Match` on manifest fetches.** Marginal bandwidth savings
  given the manifest is ~500 bytes and we already digest-compare
  locally. Worth it only if poll interval drops well below 60 s.
- **Secure Boot v2 + Flash Encryption.** Hardware-rooted trust and
  confidentiality. Irreversible eFuse burns. Closes the soft-trust
  gap above.
- **NVS encryption** without Secure Boot — limited value (any flasher
  can disable it without Secure Boot to root the chain), but trivial
  to enable. Probably not worth it alone.
- **Provisioning over BLE or Wi-Fi AP** — for at-scale fleet
  provisioning. Standard ESP-IDF `wifi_provisioning` component
  handles this. Adds firmware size; only worth it if we ever ship
  more than one device.
- **Remote re-provisioning of non-secret keys** (poll interval, log
  severity, etc.) via the OTA channel — push small "config artifacts"
  alongside firmware artifacts in OCI. Combined with the next bullet,
  enables seamless SA-key rotation.
- **Rotating the SA key** — currently means re-provisioning every
  device over USB. With remote re-provisioning above, becomes a push
  button.
