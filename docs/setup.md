# Setup

End-to-end first-time setup for an Inland ESP-WROOM-32 dev board on
macOS.

## Hardware

- **Board**: Inland ESP-WROOM-32 (Micro Center SKU 027466, rebadged
  Keyestudio KS0413, "mini" form factor). Connects as
  `/dev/cu.usbserial-0001` over the onboard CP210x USB-UART.
- **No user LED** on this variant — only a power LED ("D1", hardwired
  to 3V3, always on). The DOIT/DEVKITC-style blue LED on GPIO 2 is
  *not* populated. Watch boot via `make monitor`.

## One-time host install

```bash
cargo install espup espflash ldproxy
brew install cmake ninja dfu-util cosign jq
espup install --targets esp32
curl -LsSf https://astral.sh/uv/install.sh | sh   # if you don't have uv
```

`uv` provides Python 3.12 for ESP-IDF's tooling — see [why](#python-shim) below.

## Provisioning

```bash
make provisioning.toml             # creates from template
$EDITOR provisioning.toml          # fill in wifi creds + trust identities
make bootstrap                     # build, flash everything, write NVS
make monitor                       # watch it boot and connect
```

The first build clones ESP-IDF v5.2.2 into `.embuild/` (5–10 min).
Subsequent builds are fast.

The OTA-distributed firmware contains **no secrets** — Wi-Fi creds,
Sigstore trust roots, and (optionally) GCP service-account keys all
live in NVS, written via USB by `make provision`. See
[`ota.md`](ota.md) for the full design.

## Day-to-day Make targets

```
make build      Compile firmware
make flash      Build + flash app (use flash-all after partitions change)
make flash-all  Erase + write bootloader, partition table, app
make provision  Write NVS partition from provisioning.toml over USB
make bootstrap  flash-all + provision (new device setup)
make monitor    Open serial monitor; Ctrl+C to exit
make run        Build + flash + monitor
make publish    Build, push OCI artifact to ghcr.io/imjasonh/esp32, cosign sign
make clean      cargo clean
```

`make publish` requires `gh.env` (see [`ota.md`](ota.md) for PAT setup)
and a real cosign OIDC flow the first time per ~10 min window — a
browser pops to authenticate. CI does this automatically via the
GitHub Actions workflow's ambient OIDC token.

## Optional: GCP Cloud Logging + Monitoring

The firmware can ship structured `tracing` events to **Cloud
Logging** and chip-health metrics (heap, stack, wifi, cpu, …) to
**Cloud Monitoring**. Both are opt-in per device — without a `[gcp]`
block in `provisioning.toml`, the device boots normally and emits to
serial only. Full design in [`observability.md`](observability.md).

One service account and one key cover both APIs. One-time GCP setup:

```bash
PROJECT_ID=<YOUR_PROJECT_ID>
SA_NAME=<YOUR_SA_NAME>
SA_EMAIL=$SA_NAME@$PROJECT_ID.iam.gserviceaccount.com

# Create the service account.
gcloud iam service-accounts create $SA_NAME \
    --display-name="ESP32 device logger" \
    --project=$PROJECT_ID

# Grant only logging.logWriter + monitoring.metricWriter — least
# privilege. The device can write log entries and metric points;
# nothing else.
gcloud projects add-iam-policy-binding $PROJECT_ID \
    --member="serviceAccount:$SA_EMAIL" \
    --role="roles/logging.logWriter"
gcloud projects add-iam-policy-binding $PROJECT_ID \
    --member="serviceAccount:$SA_EMAIL" \
    --role="roles/monitoring.metricWriter"

# Create + download a JSON key. Keep this file safe — anyone with it
# can write logs + metrics as this SA.
gcloud iam service-accounts keys create gcp-sa-key.json \
    --iam-account=$SA_EMAIL \
    --project=$PROJECT_ID

# Extract the RSA private key PEM and the key id into the forms
# `tools/provision/` wants. Use `jq -j` (no trailing newline) — the
# device-side PEM parser is strict.
jq -j .private_key    gcp-sa-key.json > gcp-sa-key.pem
KEY_ID=$(jq -r .private_key_id gcp-sa-key.json)
echo "sa_key_id = $KEY_ID"
```

Then add a `[gcp]` block to `provisioning.toml` (template in
`provisioning.toml.example`) using `$PROJECT_ID`, `$SA_EMAIL`, the
printed `KEY_ID`, and the path `gcp-sa-key.pem`. Re-run `make
provision` and reboot the device.

Inspect what's flowing in:

```bash
# Logs (Cloud Logging)
gcloud logging read \
    'logName="projects/'"$PROJECT_ID"'/logs/esp32-firmware"' \
    --limit=20 --project=$PROJECT_ID

# Metrics (Cloud Monitoring) — one metric type at a time
TOKEN=$(gcloud auth print-access-token)
START=$(date -u -v-30M +%Y-%m-%dT%H:%M:%SZ)
END=$(date -u +%Y-%m-%dT%H:%M:%SZ)
curl -sG "https://monitoring.googleapis.com/v3/projects/$PROJECT_ID/timeSeries" \
    -H "Authorization: Bearer $TOKEN" \
    --data-urlencode 'filter=metric.type="custom.googleapis.com/esp32/free_heap"' \
    --data-urlencode "interval.startTime=$START" \
    --data-urlencode "interval.endTime=$END" | jq
```

**Threat model**: the SA private key sits in NVS unencrypted. Anyone
with physical access to the chip can extract it. Mitigation is strict
SA scoping (see roles above) and a logs/metrics-only project. Real
hardening = Flash Encryption + Secure Boot v2 (deferred; see
[`ota.md`](ota.md) Future work).

## <a name="python-shim"></a>Python 3.12 shim

embuild bootstraps the ESP-IDF venv using whatever `python3` is first
on `PATH`. On macOS that's Apple's `/usr/bin/python3` (3.9.6). ESP-IDF
v5.2 nominally supports 3.8–3.12, but pip dependency resolution on
3.9 silently drops some transitive deps (notably `ruamel.yaml` and its
dependents) and IDF's check then fails with cryptic "Failed to run
Python dependency check ... Error: 255".

Fix: the Makefile creates `.embuild/python-shim/python3` as a symlink
to a uv-managed Python 3.12 and prepends that directory to `PATH` for
every recipe. The shim isn't checked in — it's regenerated by the
`ensure-python-shim` Make target, a prerequisite of `build`.

If you hit the dependency-check error after upgrading or after a fresh
clone:

```bash
rm -rf .embuild
make build
```
