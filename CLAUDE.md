# Project notes for Claude

## Project layout

```
src/main.rs                 firmware entrypoint, Wi-Fi + boot orchestration
src/ota.rs                  OTA poll loop, manifest fetch, blob streaming
src/sig.rs                  cosign Sigstore Bundle verification
src/trust.rs                NVS-loaded trust config (signer identities + Sigstore CAs)
src/cloud_log.rs            tracing → Cloud Logging (queue + sender thread)
src/metrics.rs              chip-health snapshots → Cloud Monitoring time series
src/gcp_auth.rs             multi-scope JWT mint, shared TokenProvider, ShortHttpsLock,
                            OtaDownloadGuard, HTTPS helpers
trust/                      Sigstore Fulcio root + intermediate certs (provisioned via NVS)
tools/publisher/            host-side tool that pushes signed OCI artifacts to GHCR
tools/provision/            host-side tool that builds + flashes NVS partition
.github/workflows/          ci.yml (PRs) + publish.yml (push to main)
Cargo.toml                  firmware deps
partitions.csv              OTA-capable partition table (1.94 MB app slots)
sdkconfig.defaults.in       ESP-IDF kconfig template (Makefile substitutes paths)
Makefile                    build / flash / monitor / provision / publish entrypoints
provisioning.toml.example   template for per-device NVS values
docs/setup.md               first-flash + day-to-day workflow + GCP setup
docs/ota.md                 full OTA + provisioning + signing system documentation
docs/observability.md       Cloud Logging + Monitoring design (current state)
docs/eink-plan.md           planned e-ink display work
README.md                   short top-level overview, links into docs/
```

## Conventions established in this repo

- **`docs/` for descriptive docs and per-feature plans.** Forward-
  looking work uses `<feature>-plan.md`; once shipped, the plan is
  rewritten in present tense and lives next to the other reference
  docs (e.g. `logs-plan.md` + `monitoring-plan.md` collapsed into
  `docs/observability.md`).
- **Cargo.lock IS tracked** for all three crates here — they're all
  binaries.
- **Don't use "and" in Make target names** — chain existing targets
  instead (`make publish monitor`, not `make publish-and-monitor`).
- **Env-setup scripts** (e.g. espup's `export-esp.sh`) live in the
  project dir, not `~`.
- **GHCR auth** uses classic PATs with `write:packages` (fine-grained
  PATs don't expose a Packages permission for user-owned packages).
- **Use `make` targets**, not raw `espflash`/`cargo` commands. The
  Makefile sets toolchain env, the Python 3.12 shim, and (critically)
  always passes `--partition-table partitions.csv` to `espflash flash`
  — without that, espflash 4.x silently writes a default
  factory-only partition table over our OTA layout.

## Architectural decisions worth knowing

- **std Rust on top of ESP-IDF**, not no_std with `esp-hal`. We need
  easy Wi-Fi + HTTP + TLS via `esp-idf-svc`, plus standard
  threading/heap. The cost is ESP-IDF's C SDK + CMake/Ninja/Python
  toolchain; the lighter no_std path is worth knowing for future
  projects.
- **Pure-Rust `rsa` crate for JWT signing**, not mbedtls FFI. Adds
  ~50 KB but keeps the code in safe Rust.
- **mbedtls heap is tight.** With cloud_log + metrics + OTA each
  potentially holding a TLS session, three concurrent handshakes
  (~25–35 KB each) blow our heap. Mitigations stacked in
  `sdkconfig.defaults.in` (`MBEDTLS_DYNAMIC_BUFFER`, free
  config/CA-cert, `KEEP_PEER_CERTIFICATE=n`) plus runtime serialization
  via `gcp_auth::ShortHttpsLock` and an `OTA_DOWNLOAD_IN_PROGRESS`
  gate. See `docs/observability.md` for the full chain.
- **OTA download is *not* serialized.** Multi-second blob downloads
  must not block per-5 s log flushes. cloud_log + metrics check
  `OTA_DOWNLOAD_IN_PROGRESS` and skip-but-don't-drain while a
  download is in flight; the queue absorbs and flushes after.

## Gotchas to remember

- **Custom partition table path resolution.** ESP-IDF resolves
  `CONFIG_PARTITION_TABLE_CUSTOM_FILENAME` relative to its top-level
  CMake project, which for embuild is `target/.../esp-idf-sys-<hash>/out/`,
  not the repo root. Workaround: `sdkconfig.defaults.in` is the
  template (committed), with the placeholder
  `@PROJECT_DIR@/partitions.csv`; the Makefile substitutes the
  absolute path at build time and writes the resolved
  `sdkconfig.defaults` (gitignored). Don't "fix" the placeholder.
- **Python 3.12 shim.** embuild grabs whatever `python3` is first on
  PATH. macOS's default is 3.9.6, which silently breaks ESP-IDF
  dependency resolution. The Makefile creates
  `.embuild/python-shim/python3 → uv-managed 3.12` and prepends it to
  PATH. If a dep-check error appears after a fresh clone:
  `rm -rf .embuild && make build`.
- **No user LED on this board.** Inland ESP-WROOM-32 has only a
  power LED; the DOIT/DEVKITC blue LED on GPIO 2 is *not* populated.
  Don't suggest GPIO blink demos — use serial logging via `make
  monitor` instead.
- **NVS key names cap at 15 characters.** When adding new keys to
  `tools/provision/`, abbreviate (`metric_intvl`, not
  `metrics_interval`). The `.toml` field can be long and readable;
  the NVS key is the constrained one.
- **`make flash` after a fresh `make bootstrap`** can boot the wrong
  partition: bootstrap clears otadata so the bootloader picks ota_0,
  but a subsequent OTA download installs to ota_1 and otadata starts
  pointing there. A bare `make flash` writes to ota_0 (the first app
  partition in the table) but the device will keep booting ota_1
  until you `make bootstrap` again or wait for OTA promotion.
