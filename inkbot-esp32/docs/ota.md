# OTA, NVS provisioning, and optional GCP

This page is for someone flashing a Waveshare ESP32 desk frame. It covers
the first USB write, how the device picks up later images, and how to ship
logs and metrics to Google Cloud.

Secrets never go in the ELF. Wi-Fi, the Worker URL, Sigstore trust, the
optional service-account key, and OTA overrides live in the NVS partition
that `make provision` writes. An OTA image can replace the app slots without
touching those keys.

## First flash on a board that already has factory firmware

Today's in-field image uses a single factory partition. This firmware uses
two OTA slots and a different NVS layout, so a USB **erase + flash-all +
provision** is required once. You cannot OTA from the pre-OTA image.

```bash
cd inkbot-esp32
cp provisioning.toml.example provisioning.toml
# Edit wifi, inkbot.base_url, and (optionally) [gcp] / [ota].
make bootstrap PORT=/dev/cu.usbserial-XXXX   # Linux: PORT=/dev/ttyUSB0
make monitor
```

`make bootstrap` erases flash, writes the bootloader, the OTA partition
table, the inkbot app, and the NVS image. After that, later updates can
arrive over GHCR.

If Wi-Fi or trust keys are missing, the panel shows `NOT PROVISIONED` and
the serial log repeats the same message.

`inkbot.base_url` must start with `https://` (the provisioner and the
firmware both reject plaintext). `make provision` does not rebuild the
app; run `make build` once so ESP-IDF's NVS generator is present, then
re-provision as often as you need. `make provision-build` writes
`target/nvs.bin` without flashing.

Re-running `make provision` replaces the entire NVS partition. These keys
are wiped:

- Runtime keys in the `inkbot` namespace (`name`, `etag`, `latest`, `op`,
  `inc`). The device treats the catalog as new on the next boot.
- OTA digest cache (`ota/last_digest`, `ota/pending_digest`). The next
  poll re-downloads `:latest` even when GHCR has not changed.

## What you put in `provisioning.toml`

| Section | Required | What it does |
|---------|----------|--------------|
| `[wifi]` | yes | `ssid` and `pass` (empty `pass` is an open network) |
| `[inkbot]` | yes | Worker `base_url` plus poll / rotate / status / DHCP intervals |
| `[trust]` | yes | Fulcio PEMs and the identities allowed to sign OTA images |
| `[gcp]` | no | Cloud Logging + Monitoring. Omit for serial-only logs |
| `[ota]` | no | Overrides the compiled default app / repo / tag / poll interval |

`inkbot.upload_secret` must match the Worker's `UPLOAD_SECRET` if you want
`POST /device`. Leave it empty to keep telemetry on the panel and serial
only.

`ota.poll_secs = 0` disables GHCR polling (USB flash only). If you omit
`[ota]`, the firmware polls `ghcr.io/imjasonh/playground/inkbot-esp32:latest`
every 600 seconds. Set `ota.app = "maze-esp32"` (and omit `repo`, or set it
to the maze package) so a running inkbot image pulls maze instead. Maze
never polls GHCR, so that switch is one-way until you USB-flash inkbot.

The example file already allowlists two signers:

- A Google account for a laptop `make publish`
- The `inkbot-esp32-publish.yml` workflow on `main` for CI

If you publish from another identity, add it under `[[trust.identities]]`
and re-run `make provision`.

## Optional Google Cloud logs and metrics

The firmware does not take the official Google client crates. A small client
mints a JWT with mbedTLS (already linked for HTTPS), exchanges it for an
access token, and POSTs to Cloud Logging and Cloud Monitoring. That keeps
RSA / tracing / time crates out of the image.

1. Create a service account in the project that should receive logs.
2. Grant `roles/logging.logWriter` and `roles/monitoring.metricWriter`.
   The first custom metric descriptor create can also need
   `roles/monitoring.admin` once.
3. Create a JSON key. Extract the PKCS#8 PEM and fields:

   ```bash
   jq -r .private_key sa.json > gcp-sa-key.pem
   chmod 600 gcp-sa-key.pem
   ```

   Use `client_email` as `sa_email` and `private_key_id` as `sa_key_id`.
   Keep the PEM out of the git worktree when you can; the filename
   `gcp-sa-key.pem` is gitignored if you leave it in `inkbot-esp32/`.
4. Uncomment `[gcp]` in `provisioning.toml` and run `make provision`.
   To leave GCP out of the ELF entirely, build with `make build GCP=0`.

On boot the device tees `log` records into a 64-entry queue and flushes
batches from the main loop (the same loop that paints the panel). It does
not start a GCP thread. During an OTA blob download, flushes are skipped so
two TLS sessions do not fight the 48 KB framebuffer for heap.

Metrics (when `metrics_interval_secs` is not 0) are gauges on
`custom.googleapis.com/inkbot/*`: free heap, min free heap, largest 8-bit
block, uptime, Wi-Fi RSSI, and log-queue depth / drops. The resource type
is `generic_node` with `node_id` set to the chip MAC.

## How OTA works after bootstrap

Every `ota.poll_secs` (default 10 minutes), after a 30-second boot grace
period, the inkbot binary:

1. Fetches an anonymous GHCR pull token and the OCI manifest for
   `repo:tag` (`repo` defaults to `ghcr.io/imjasonh/playground/{ota/app}`).
2. Skips the rest if the layer digest matches the last successful (or
   rejected) digest in NVS.
3. Fetches the OCI config blob and requires `app` to equal the requested
   `ota/app` (default `inkbot-esp32`), `target_chip=esp32`, and a layer
   that fits the `0x1F0000` slot. A maze image is valid when `ota/app` is
   `maze-esp32`.
4. Pulls the Cosign signature: first `sha256-<manifest>.sig` (Cosign 2.5
   simple-signing), then `sha256-<manifest>` (Sigstore bundle). Checks the
   Fulcio leaf SAN + OIDC issuer against `trust/identities`, verifies the
   chain, and checks the signed payload binds the firmware manifest digest.
5. Streams the firmware blob into the inactive slot, hashing as it goes.
6. Marks that slot to boot and restarts.

On the new image, ESP-IDF leaves the slot in `PENDING_VERIFY`. inkbot
marks the image valid only after the Worker boot fetch succeeds
(`Displayed` or empty catalog). maze marks valid after the first
successful panel paint. A failed health check in that window calls
`esp_ota_mark_app_invalid_rollback_and_reboot()` and records the digest as
rejected so the next poll does not re-flash the same binary.

The on-device verifier does not check Fulcio certificate transparency
SCTs or the leaf EKU. The identity allowlist plus the pinned Fulcio
PEMs in NVS are the trust boundary.

OTA runs on the inkbot main task (48 KB stack). Frame fetches and GCP posts
pause while the blob download holds a TLS session. The maze binary never
joins Wi-Fi and never polls GHCR. inkbot can still *install* maze over OTA
when `ota/app` is `maze-esp32`; returning to inkbot is `make flash`.

The GHCR packages must be **public**. The device uses an anonymous pull
token. After the first CI publish, open
[the package settings](https://github.com/imjasonh/playground/pkgs)
and change visibility if GitHub created them as private.

## Publish a new image

CI: a push to `main` that touches `inkbot-esp32/` (or a manual *Run
workflow* **from `main`**) runs `.github/workflows/inkbot-esp32-publish.yml`.
That job cross-compiles both apps, pushes
`ghcr.io/imjasonh/playground/inkbot-esp32:latest` and
`ghcr.io/imjasonh/playground/maze-esp32:latest` plus `:sha-<git>` on each,
keyless-signs the digests with Cosign, then `make pull-verify`s both layers.
Devices that already trust the workflow identity pick it up on the next
poll. Dispatch from any other branch is skipped: keyless Cosign would
produce `@refs/heads/<branch>`, which the example allowlist rejects.

From a laptop (identity must be in `trust/identities`):

```bash
cd inkbot-esp32
echo 'export GH_TOKEN=ghp_xxxxxxxx' > gh.env   # packages:write
brew install cosign
make publish
```

`make publish` needs `espflash` 4.5.0 (`save-image --ignore-app-descriptor`),
`cosign`, and a
token that can write the package.

## Flash and RAM budget

The Waveshare driver board is a classic ESP32 with 4 MB flash. The OTA
table is two slots of `0x1F0000` (1.9375 MiB) each. There is no leftover
flash for a factory partition.

TLS record buffers are 8 KiB in / 2 KiB out (Google OAuth chains need
more than 4 KiB). The CA store is the PEMs
in `certs/` (Let's Encrypt, Google Trust Services, DigiCert, USERTrust,
and GlobalSign Root CA) instead of the full Mozilla bundle. Cloudflare
Workers presents GTS Root R4 cross-signed by GlobalSign, and ESP-IDF's
bundle callback looks up that issuer. Keep the list short; a full
bundle plus the 48 KB framebuffer does not fit in DRAM next to Wi-Fi.

Do not add an OTA thread or hold the last framebuffer during a GHCR
download. Those are the two ways this board OOMs.

## Maze firmware

`APP=maze` builds a second ELF with `sdkconfig.defaults.maze.in` (no CA
bundle, smaller stack, Wi-Fi driver requested off) into
`target/maze-esp32/`. It does not compile inkbot-lib, OTA-pull, or GCP.

You can put maze on the panel two ways:

- USB: `make flash APP=maze`
- OTA from a running inkbot image: set `[ota] app = "maze-esp32"` in
  `provisioning.toml`, `make provision`, and wait for the next poll

Maze never joins Wi-Fi, so it cannot pull inkbot back. To return to the
frame loop, USB-flash without `APP=maze`.
