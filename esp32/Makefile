# ESP32 Rust — runnable documentation for build / flash / monitor.
# See docs/setup.md for one-time setup (espup, brew deps, Python 3.12 shim).
#
# Quick start (new device):
#   make provisioning.toml   # one-time: copy template
#   $EDITOR provisioning.toml  # fill in wifi creds, trust identities
#   make bootstrap           # full reflash + write NVS partition
#   make monitor             # watch it boot + connect

PORT ?= /dev/cu.usbserial-0001
APP  ?= blinky

ifeq ($(APP),blinky)
PACKAGE            := esp32-blinky
TARGET_DIR         := target/blinky
BIN                := $(TARGET_DIR)/xtensa-esp32-espidf/release/esp32-blinky
SDKCONFIG_TEMPLATE := sdkconfig.defaults.in
SDKCONFIG_DEFAULTS := sdkconfig.defaults
OCI_REPO           ?= ghcr.io/imjasonh/esp32
else ifeq ($(APP),eink)
PACKAGE            := esp32-eink
TARGET_DIR         := target/eink
BIN                := $(TARGET_DIR)/xtensa-esp32-espidf/release/esp32-eink
SDKCONFIG_TEMPLATE := eink/sdkconfig.defaults.in
SDKCONFIG_DEFAULTS := eink/sdkconfig.defaults
OCI_REPO           ?= ghcr.io/imjasonh/esp32-eink
else
$(error Unknown APP '$(APP)'; expected APP=blinky or APP=eink)
endif

# Host triple for building host-side tools (publisher, provision).
HOST_TRIPLE := $(shell rustc -vV | sed -n 's/^host: //p')

# App-only firmware binary (no bootloader / partition table) suitable for
# pushing as the OTA artifact layer.
FW_BIN := target/$(APP)-firmware.bin
OTA_SLOT_BYTES := 2031616

# Generated NVS partition image written by `tools/provision/`.
NVS_BIN := target/nvs.bin

# Username for cosign's registry auth (its own auth, separate from the
# OIDC identity used to sign). Override with COSIGN_REGISTRY_USERNAME=...
# in CI to use the workflow's actor.
COSIGN_REGISTRY_USERNAME ?= imjasonh

# Short git SHA, baked into the firmware via env!() (see build.rs + main.rs)
# and used as the secondary OCI tag on publish.
GIT_SHA := $(shell git rev-parse --short HEAD 2>/dev/null || echo unknown)
export GIT_SHA

# Toolchain paths installed by `espup install --targets esp32`. The
# wildcards absorb the date-stamped subdirectory names so espup upgrades
# don't require editing this file.
RUSTUP_HOME    := $(shell rustup show home 2>/dev/null)
LIBCLANG_PATH  := $(firstword $(wildcard $(RUSTUP_HOME)/toolchains/esp/xtensa-esp32-elf-clang/*/esp-clang/lib))
XTENSA_GCC_BIN := $(firstword $(wildcard $(RUSTUP_HOME)/toolchains/esp/xtensa-esp-elf/*/xtensa-esp-elf/bin))

# A throwaway directory containing `python3` -> uv-managed Python 3.12.
# Put on PATH ahead of system python so embuild bootstraps the IDF venv
# against 3.12 instead of Apple's /usr/bin/python3 (3.9). Created on demand
# by the `ensure-python-shim` target — not checked in.
PYTHON_SHIM := $(CURDIR)/.embuild/python-shim

# Exported to every recipe shell. Replaces the old export-esp.sh script.
export LIBCLANG_PATH
export PATH := $(PYTHON_SHIM):$(XTENSA_GCC_BIN):$(PATH)
# A custom absolute path keeps ESP-IDF shared by the app-specific Cargo target
# directories. Without this, embuild puts a separate copy under target/.
export ESP_IDF_TOOLS_INSTALL_DIR := custom:$(CURDIR)/.embuild

.PHONY: help build flash flash-all monitor run clean ensure-python-shim \
        save-image check-image-size publish pull-verify check-gh-env \
        provision provision-build bootstrap

help:
	@echo "Targets:"
	@echo "  make build         Compile firmware (APP=blinky or APP=eink)"
	@echo "  make flash         Build (if needed) and flash app to $(PORT)"
	@echo "  make flash-all     Erase + write bootloader, partition table, app"
	@echo "  make monitor       Open serial monitor on $(PORT)  (Ctrl+C to exit)"
	@echo "  make run           Build + flash + monitor"
	@echo "  make clean         cargo clean"
	@echo "  make save-image    Convert ELF -> app-only .bin (target/firmware.bin)"
	@echo "  make check-image-size  Reject firmware that cannot fit an OTA slot"
	@echo "  make publish       Build, save-image, push OCI artifact to OCI_REPO"
	@echo "  make pull-verify   Pull from OCI_REPO and check layer matches local .bin"
	@echo ""
	@echo "  make provision     Build NVS image from provisioning.toml + flash to device"
	@echo "  make bootstrap     flash-all + provision (new device setup)"
	@echo ""
	@echo "Select the e-ink client: make APP=eink build"
	@echo "Override the port: make APP=eink flash PORT=/dev/cu.usbserial-XXXX"

build: ensure-python-shim $(SDKCONFIG_DEFAULTS)
	# `+esp` selects the espup-installed toolchain explicitly. We don't
	# use `rust-toolchain.toml` for the firmware crate anymore because
	# Dependabot's runner doesn't have the esp toolchain installed and
	# `cargo update` chokes on the override file. Host-side tools have
	# their own `rust-toolchain.toml` pinning stable.
	ESP_IDF_SDKCONFIG_DEFAULTS=$(SDKCONFIG_DEFAULTS) \
	    cargo +esp build --release --package $(PACKAGE) --target-dir $(TARGET_DIR)

# sdkconfig.defaults is generated from the .in template so we can substitute
# the absolute project path into CONFIG_PARTITION_TABLE_CUSTOM_FILENAME
# (IDF resolves it relative to the embuild synthetic project, not our repo
# root, so a bare "partitions.csv" doesn't work). Gitignored.
$(SDKCONFIG_DEFAULTS): $(SDKCONFIG_TEMPLATE) partitions.csv
	@sed 's|@PROJECT_DIR@|$(CURDIR)|g' $(SDKCONFIG_TEMPLATE) > $(SDKCONFIG_DEFAULTS)

# Idempotent: creates $(PYTHON_SHIM) and (re)points python3 at the current
# uv-managed 3.12 interpreter. Auto-installs Python 3.12 via uv if missing.
#
# Important: nuke any pre-existing shim symlinks first. If the shim dir was
# restored from a CI cache, the symlinks may target a path that no longer
# exists on this runner, OR may have been auto-resolved by `uv python find`
# back to the shim itself (self-reference) producing ELOOP. Recreating
# from scratch each run avoids both.
ensure-python-shim:
	@command -v uv >/dev/null || { echo "ERROR: uv not installed. See docs/setup.md."; exit 1; }
	@mkdir -p $(PYTHON_SHIM)
	@rm -f $(PYTHON_SHIM)/python $(PYTHON_SHIM)/python3
	@uv python install 3.12 >/dev/null
	@PY=$$(uv python find --managed-python 3.12) && \
	    ln -sf "$$PY" $(PYTHON_SHIM)/python3 && \
	    ln -sf "$$PY" $(PYTHON_SHIM)/python

# Pass --partition-table on every flash, even app-only. Without it,
# espflash 4.x writes a *default* (factory-only) partition table over
# our OTA layout — silently bricking OTA on the device. Re-passing
# partitions.csv is a no-op when it already matches what's on flash.
flash: build
	espflash flash --port $(PORT) --partition-table partitions.csv $(BIN)

# Full reflash: erase entire flash, then write bootloader + partition table
# + app. Use this when the partition table changes, or as the recovery
# path if both OTA slots are bad and anti-bricking failed. After erase,
# otadata is empty and the bootloader picks ota_0 by default. NVS is also
# wiped, so the device will boot strict-inert until `make provision`.
BOOTLOADER := $(firstword $(wildcard $(TARGET_DIR)/xtensa-esp32-espidf/release/build/esp-idf-sys-*/out/build/bootloader/bootloader.bin))

flash-all: build
	@test -n "$(BOOTLOADER)" || { echo "ERROR: bootloader.bin not found under target/. Run 'make build' first."; exit 1; }
	espflash erase-flash --port $(PORT)
	espflash flash --port $(PORT) \
	    --bootloader $(BOOTLOADER) \
	    --partition-table partitions.csv \
	    $(BIN)

monitor:
	espflash monitor --port $(PORT) $(if $(MAKE_TERMOUT),,--non-interactive)

run: build
	espflash flash --port $(PORT) --partition-table partitions.csv --monitor $(BIN)

clean:
	cargo clean

# Build NVS partition image from provisioning.toml AND flash it to the
# device over USB. Requires `make build` to have run at least once so
# embuild has cloned ESP-IDF (needed for nvs_partition_gen.py).
provision: provisioning.toml build
	cd tools/provision && cargo run --release --target $(HOST_TRIPLE) -- \
	    --config $(CURDIR)/provisioning.toml \
	    --out $(CURDIR)/$(NVS_BIN) \
	    --nvs-gen $(NVS_GEN_PY) \
	    --python $(NVS_GEN_PYTHON) \
	    --port $(PORT) \
	    --flash

# Build the NVS image without flashing (useful for inspection / CI).
provision-build: provisioning.toml build
	cd tools/provision && cargo run --release --target $(HOST_TRIPLE) -- \
	    --config $(CURDIR)/provisioning.toml \
	    --out $(CURDIR)/$(NVS_BIN) \
	    --nvs-gen $(NVS_GEN_PY) \
	    --python $(NVS_GEN_PYTHON)

# ESP-IDF's NVS partition generator + the python venv to run it in.
# Both come from .embuild after `make build` has cloned ESP-IDF.
NVS_GEN_PY     := $(CURDIR)/.embuild/esp-idf/v5.2.2/components/nvs_flash/nvs_partition_generator/nvs_partition_gen.py
NVS_GEN_PYTHON := $(CURDIR)/.embuild/python_env/idf5.2_py3.12_env/bin/python

# Common new-device setup: full reflash + provision NVS. After this the
# device should boot, connect to Wi-Fi, and start polling for OTAs.
bootstrap: flash-all provision

# If provisioning.toml exists, this target is up-to-date and the recipe
# doesn't run. If absent, copy the template, tell the user to edit it,
# and fail so they can't accidentally provision with placeholder values.
provisioning.toml:
	@cp provisioning.toml.example provisioning.toml
	@echo ""
	@echo "Created provisioning.toml from provisioning.toml.example."
	@echo "Edit it with your real Wi-Fi creds + trust identities, then re-run."
	@echo ""
	@exit 1

# Convert the firmware ELF into an app-only .bin (no bootloader / partition
# table). This is the format the OTA writer expects on the device, and what
# we wrap as an OCI artifact layer for OTA distribution.
save-image: $(FW_BIN)

$(FW_BIN): build
	espflash save-image --chip esp32 $(BIN) $(FW_BIN)
	@echo "Wrote $(FW_BIN) ($$(wc -c < $(FW_BIN)) bytes)"

check-image-size: $(FW_BIN)
	@SIZE=$$(wc -c < $(FW_BIN)); \
	    echo "$(APP) firmware: $$SIZE bytes; OTA slot: $(OTA_SLOT_BYTES) bytes"; \
	    test "$$SIZE" -le "$(OTA_SLOT_BYTES)" || { \
	        echo "ERROR: firmware exceeds OTA slot by $$((SIZE - $(OTA_SLOT_BYTES))) bytes"; \
	        exit 1; \
	    }

# Build firmware -> save-image -> push OCI artifact to OCI_REPO. Tags
# pushed: :latest and :sha-<short>. Requires GH_TOKEN in gh.env.
#
# `set -eo pipefail` so a publisher crash doesn't get swallowed by the
# `| grep | head | cut` pipeline and silently produce an empty DIGEST
# (we'd catch it with the test below, but pipefail makes the original
# error message visible).
#
# Target-specific SHELL := bash because `pipefail` isn't a POSIX
# `set -o` option — the default `/bin/sh` on Ubuntu (dash) rejects it
# with "Illegal option -o pipefail" before any other command runs. We
# only need bash for this one recipe; everything else stays on /bin/sh.
publish: SHELL := /bin/bash
publish: check-image-size check-gh-env
	@set -eo pipefail; \
	    . ./gh.env; \
	    DIGEST=$$(cd tools/publisher && cargo run --release --target $(HOST_TRIPLE) -- push \
	        --bin $(CURDIR)/$(FW_BIN) \
	        --repo $(OCI_REPO) \
	        --app-id $(APP) \
	        --max-bin-size $(OTA_SLOT_BYTES) \
	        --source https://github.com/imjasonh/playground \
	        --git-sha $(GIT_SHA) | grep '^digest:' | head -1 | cut -d' ' -f2); \
	    test -n "$$DIGEST" || { echo "ERROR: publisher did not emit a 'digest:' line on stdout"; exit 1; }; \
	    echo ">>> Signing $(OCI_REPO)@$$DIGEST with cosign (keyless OIDC)"; \
	    COSIGN_REGISTRY_USERNAME=$(COSIGN_REGISTRY_USERNAME) COSIGN_REGISTRY_PASSWORD="$$GH_TOKEN" \
	        cosign sign --yes $(OCI_REPO)@$$DIGEST

# Pull the latest artifact from OCI_REPO and verify its layer SHA matches
# our locally-built firmware. Confirms the round trip works.
pull-verify: $(FW_BIN) check-gh-env
	. ./gh.env && cd tools/publisher && cargo run --release --target $(HOST_TRIPLE) -- pull-verify \
	    --repo $(OCI_REPO) \
	    --tag latest \
	    --bin $(CURDIR)/$(FW_BIN) \
	    --auth

check-gh-env:
	@test -f gh.env || { \
	    echo "ERROR: gh.env not found."; \
	    echo "Create it with:"; \
	    echo "    echo 'export GH_TOKEN=ghp_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx' > gh.env"; \
	    echo "See README.md for how to mint a classic PAT with write:packages."; \
	    exit 1; \
	}
