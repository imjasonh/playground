# inkbot-esp32 — build / flash / provision / publish helpers.
#
# One-time host setup (macOS):
#   cargo install espup espflash ldproxy
#   brew install cmake ninja dfu-util cosign jq
#   espup install --targets esp32
#   curl -LsSf https://astral.sh/uv/install.sh | sh
#
# New device:
#   make provisioning.toml
#   $EDITOR provisioning.toml
#   make bootstrap
#   make monitor
#
# Per-app images use separate CARGO_TARGET_DIR + sdkconfig trees so maze
# does not inherit Wi-Fi / CA-bundle from inkbot (Cargo features are
# per-package, not per-bin). `GCP=0` compiles GCP out of the inkbot image.

SHELL := /bin/bash

PORT ?= $(firstword $(wildcard /dev/cu.usbmodem* /dev/cu.usbserial-* /dev/ttyACM* /dev/ttyUSB*))
ifeq ($(PORT),)
PORT := /dev/cu.usbserial-0001
endif
TARGET := xtensa-esp32-espidf
APP ?= inkbot
GCP ?= 1
HOST_TRIPLE := $(shell rustc -vV | sed -n 's/^host: //p')

# Host tests and tools. Firmware recipes override this per app.
override CARGO_TARGET_DIR := $(CURDIR)/target
export CARGO_TARGET_DIR

INKBOT_TARGET_DIR := $(CURDIR)/target/inkbot-esp32
MAZE_TARGET_DIR := $(CURDIR)/target/maze-esp32
INKBOT_BIN := $(INKBOT_TARGET_DIR)/$(TARGET)/release/inkbot-esp32
MAZE_BIN := $(MAZE_TARGET_DIR)/$(TARGET)/release/maze-esp32
INKBOT_FW_BIN := $(INKBOT_TARGET_DIR)/firmware.bin
MAZE_FW_BIN := $(MAZE_TARGET_DIR)/firmware.bin
INKBOT_SDKCONFIG_DEFAULTS := $(INKBOT_TARGET_DIR)/sdkconfig.defaults
MAZE_SDKCONFIG_DEFAULTS := $(MAZE_TARGET_DIR)/sdkconfig.defaults
INKBOT_SDKCONFIG := $(INKBOT_TARGET_DIR)/sdkconfig
MAZE_SDKCONFIG := $(MAZE_TARGET_DIR)/sdkconfig
NVS_BIN := $(CURDIR)/target/nvs.bin
INKBOT_FIRMWARE_ID := $(shell awk -F'"' '/pub const FIRMWARE_ID/ { print $$2; exit }' src/status.rs)
MAZE_FIRMWARE_ID := $(shell awk -F'"' '/MAZE_FIRMWARE_ID/ { print $$2; exit }' src/maze/mod.rs)

ifneq ($(GCP),0)
INKBOT_FEATURES := firmware,inkbot-lib,net,ota-pull,epd,gcp
else
INKBOT_FEATURES := firmware,inkbot-lib,net,ota-pull,epd
endif
MAZE_FEATURES := firmware,maze-lib

ifeq ($(APP),maze)
BIN := $(MAZE_BIN)
FIRMWARE_ID := $(MAZE_FIRMWARE_ID)
BOOTLOADER := $(firstword $(wildcard $(MAZE_TARGET_DIR)/$(TARGET)/release/build/esp-idf-sys-*/out/build/bootloader/bootloader.bin))
FLASH_DEPS := build-maze
else
BIN := $(INKBOT_BIN)
FIRMWARE_ID := $(INKBOT_FIRMWARE_ID)
BOOTLOADER := $(firstword $(wildcard $(INKBOT_TARGET_DIR)/$(TARGET)/release/build/esp-idf-sys-*/out/build/bootloader/bootloader.bin))
FLASH_DEPS := build-inkbot
endif

INKBOT_OCI_REPO ?= ghcr.io/imjasonh/playground/inkbot-esp32
MAZE_OCI_REPO ?= ghcr.io/imjasonh/playground/maze-esp32
COSIGN_REGISTRY_USERNAME ?= imjasonh
GIT_SHA := $(shell git rev-parse --short HEAD 2>/dev/null || echo unknown)
export GIT_SHA

RUSTUP_HOME    := $(shell rustup show home 2>/dev/null)
LIBCLANG_PATH  := $(firstword $(wildcard $(RUSTUP_HOME)/toolchains/esp/xtensa-esp32-elf-clang/*/esp-clang/lib))
XTENSA_GCC_BIN := $(firstword $(wildcard $(RUSTUP_HOME)/toolchains/esp/xtensa-esp-elf/*/xtensa-esp-elf/bin))
PYTHON_SHIM    := $(CURDIR)/.embuild/python-shim

export LIBCLANG_PATH
export PATH := $(PYTHON_SHIM):$(XTENSA_GCC_BIN):$(PATH)
export ESP_IDF_TOOLS_INSTALL_DIR := custom:$(CURDIR)/.embuild

NVS_GEN_PY := $(CURDIR)/.embuild/espressif/esp-idf/v5.2.2/components/nvs_flash/nvs_partition_generator/nvs_partition_gen.py
NVS_GEN_PYTHON := $(CURDIR)/.embuild/espressif/python_env/idf5.2_py3.12_env/bin/python

.PHONY: help build build-inkbot build-maze check-firmware-inkbot check-firmware-maze \
	flash flash-all monitor run clean test \
	ensure-python-shim ensure-idf save-image publish publish-one pull-verify pull-verify-one \
	provision provision-build bootstrap check-gh-env

help:
	@echo "Targets:"
	@echo "  make build          Cross-compile inkbot + maze (separate IDF trees)"
	@echo "  make flash          Build + flash $(FIRMWARE_ID) to $(PORT) (APP=$(APP))"
	@echo "  make flash APP=maze Flash the maze firmware (same OTA partition table)"
	@echo "  make build GCP=0    inkbot image without Cloud Logging / Monitoring"
	@echo "  make flash-all      Erase + write bootloader, partition table, app"
	@echo "  make provision      Write NVS from provisioning.toml (needs one prior make build)"
	@echo "  make provision-build  Build target/nvs.bin without flashing"
	@echo "  make bootstrap      flash-all + provision"
	@echo "  make publish        Push signed inkbot + maze images to GHCR"
	@echo "  make monitor        Serial monitor on $(PORT)"
	@echo "  make test           Host-side unit tests + provision dry-run"
	@echo "  make clean          cargo clean"

test:
	cargo test --lib --locked
	cargo test --manifest-path tools/publisher/Cargo.toml --locked
	cargo run --manifest-path tools/provision/Cargo.toml --locked -- \
	  --config $(CURDIR)/provisioning.toml.example \
	  --out $(CURDIR)/target/nvs-dry.bin \
	  --dry-run

$(INKBOT_SDKCONFIG_DEFAULTS): sdkconfig.defaults.in partitions.csv
	@mkdir -p $(INKBOT_TARGET_DIR)
	@sed 's|@PROJECT_DIR@|$(CURDIR)|g' sdkconfig.defaults.in > $@

$(MAZE_SDKCONFIG_DEFAULTS): sdkconfig.defaults.maze.in partitions.csv
	@mkdir -p $(MAZE_TARGET_DIR)
	@sed 's|@PROJECT_DIR@|$(CURDIR)|g' sdkconfig.defaults.maze.in > $@

# Two sequential IDF builds: different sdkconfig + features cannot share
# one CMake tree, and a combined `cargo build --bin inkbot --bin maze`
# would compile maze with Wi-Fi too (features are per-package).
build:
	$(MAKE) build-inkbot
	$(MAKE) build-maze

build-inkbot: ensure-python-shim $(INKBOT_SDKCONFIG_DEFAULTS)
	@if [ -z "$(INKBOT_FIRMWARE_ID)" ]; then \
	  echo "ERROR: could not read FIRMWARE_ID from src/status.rs"; \
	  exit 1; \
	fi
	CARGO_TARGET_DIR=$(INKBOT_TARGET_DIR) \
	ESP_IDF_SDKCONFIG_DEFAULTS=$(INKBOT_SDKCONFIG_DEFAULTS) \
	ESP_IDF_SDKCONFIG=$(INKBOT_SDKCONFIG) \
	  cargo +esp build --release \
	    --features $(INKBOT_FEATURES) \
	    --bin inkbot-esp32 \
	    --target $(TARGET) \
	    -Z build-std=std,panic_abort
	@$(MAKE) --no-print-directory check-firmware-inkbot

build-maze: ensure-python-shim $(MAZE_SDKCONFIG_DEFAULTS)
	@if [ -z "$(MAZE_FIRMWARE_ID)" ]; then \
	  echo "ERROR: could not read MAZE_FIRMWARE_ID from src/maze/mod.rs"; \
	  exit 1; \
	fi
	CARGO_TARGET_DIR=$(MAZE_TARGET_DIR) \
	ESP_IDF_SDKCONFIG_DEFAULTS=$(MAZE_SDKCONFIG_DEFAULTS) \
	ESP_IDF_SDKCONFIG=$(MAZE_SDKCONFIG) \
	  cargo +esp build --release \
	    --features $(MAZE_FEATURES) \
	    --bin maze-esp32 \
	    --target $(TARGET) \
	    -Z build-std=std,panic_abort
	@$(MAKE) --no-print-directory check-firmware-maze

check-firmware-inkbot:
	@if [ ! -f "$(INKBOT_BIN)" ]; then echo "ERROR: missing $(INKBOT_BIN)"; exit 1; fi
	@if ! grep -a -F -q "$(INKBOT_FIRMWARE_ID)" "$(INKBOT_BIN)"; then \
	  echo "ERROR: $(INKBOT_BIN) does not contain $(INKBOT_FIRMWARE_ID) (stale ELF?)"; \
	  exit 1; \
	fi
	@echo "firmware $(INKBOT_FIRMWARE_ID) -> $(INKBOT_BIN) ($$(wc -c < "$(INKBOT_BIN)") bytes ELF) features=$(INKBOT_FEATURES)"

check-firmware-maze:
	@if [ ! -f "$(MAZE_BIN)" ]; then echo "ERROR: missing $(MAZE_BIN)"; exit 1; fi
	@if ! grep -a -F -q "$(MAZE_FIRMWARE_ID)" "$(MAZE_BIN)"; then \
	  echo "ERROR: $(MAZE_BIN) does not contain $(MAZE_FIRMWARE_ID) (stale ELF?)"; \
	  exit 1; \
	fi
	@echo "firmware $(MAZE_FIRMWARE_ID) -> $(MAZE_BIN) ($$(wc -c < "$(MAZE_BIN)") bytes ELF) features=$(MAZE_FEATURES)"

# Always pass the OTA partition table. Without it, espflash 4.x writes a
# factory-only table and the next OTA poll cannot find a second slot.
flash: $(FLASH_DEPS)
	espflash flash --port $(PORT) --partition-table partitions.csv $(BIN)

flash-all: $(FLASH_DEPS)
	@test -n "$(BOOTLOADER)" || { echo "ERROR: bootloader.bin not found under target/. Run 'make build' first."; exit 1; }
	espflash erase-flash --port $(PORT)
	espflash flash --port $(PORT) \
	  --bootloader $(BOOTLOADER) \
	  --partition-table partitions.csv \
	  $(BIN)

monitor:
	espflash monitor --port $(PORT)

run: flash monitor

clean:
	cargo clean
	rm -rf .embuild sdkconfig.defaults

ensure-python-shim:
	@command -v uv >/dev/null || { echo "ERROR: uv not installed (see README)."; exit 1; }
	@command -v cargo >/dev/null || { echo "ERROR: cargo not installed."; exit 1; }
	@rustup toolchain list | grep -q '^esp' || { echo "ERROR: esp toolchain missing. Run: espup install --targets esp32"; exit 1; }
	@mkdir -p "$(PYTHON_SHIM)"
	@rm -f "$(PYTHON_SHIM)/python" "$(PYTHON_SHIM)/python3"
	@uv python install 3.12 >/dev/null
	@PY=$$(uv python find --managed-python 3.12) && \
	    ln -sfn "$$PY" "$(PYTHON_SHIM)/python3" && \
	    ln -sfn "$$PY" "$(PYTHON_SHIM)/python"

provisioning.toml:
	@cp provisioning.toml.example provisioning.toml
	@echo "Created provisioning.toml from provisioning.toml.example."
	@echo "Edit it with Wi-Fi, Worker URL, trust identities, and optional [gcp], then re-run."
	@exit 1

ensure-idf:
	@test -f "$(NVS_GEN_PY)" || { \
	  echo "ERROR: $(NVS_GEN_PY) missing. Run 'make build' once so embuild clones ESP-IDF."; \
	  exit 1; \
	}
	@test -x "$(NVS_GEN_PYTHON)" || { \
	  echo "ERROR: $(NVS_GEN_PYTHON) missing. Run 'make build' once so embuild sets up Python."; \
	  exit 1; \
	}

provision: provisioning.toml ensure-idf
	cargo run --release --manifest-path tools/provision/Cargo.toml --target $(HOST_TRIPLE) -- \
	  --config $(CURDIR)/provisioning.toml \
	  --out $(NVS_BIN) \
	  --nvs-gen $(NVS_GEN_PY) \
	  --python $(NVS_GEN_PYTHON) \
	  --port $(PORT) \
	  --flash

provision-build: provisioning.toml ensure-idf
	cargo run --release --manifest-path tools/provision/Cargo.toml --target $(HOST_TRIPLE) -- \
	  --config $(CURDIR)/provisioning.toml \
	  --out $(NVS_BIN) \
	  --nvs-gen $(NVS_GEN_PY) \
	  --python $(NVS_GEN_PYTHON)

bootstrap: flash-all provision

save-image: $(INKBOT_FW_BIN) $(MAZE_FW_BIN)

$(INKBOT_FW_BIN): build-inkbot
	@mkdir -p $(dir $@)
	espflash save-image --chip esp32 --partition-table partitions.csv $(INKBOT_BIN) $@
	@echo "Wrote $@ ($$(wc -c < $@) bytes)"

$(MAZE_FW_BIN): build-maze
	@mkdir -p $(dir $@)
	espflash save-image --chip esp32 --partition-table partitions.csv $(MAZE_BIN) $@
	@echo "Wrote $@ ($$(wc -c < $@) bytes)"

publish: SHELL := /bin/bash
publish: $(INKBOT_FW_BIN) $(MAZE_FW_BIN) check-gh-env
	$(MAKE) publish-one OCI_REPO=$(INKBOT_OCI_REPO) FW_BIN=$(INKBOT_FW_BIN) OTA_APP=inkbot-esp32
	$(MAKE) publish-one OCI_REPO=$(MAZE_OCI_REPO) FW_BIN=$(MAZE_FW_BIN) OTA_APP=maze-esp32

publish-one: SHELL := /bin/bash
publish-one: check-gh-env
	@test -n "$(OCI_REPO)" || { echo "ERROR: OCI_REPO is empty"; exit 1; }
	@test -n "$(FW_BIN)" || { echo "ERROR: FW_BIN is empty"; exit 1; }
	@test -n "$(OTA_APP)" || { echo "ERROR: OTA_APP is empty"; exit 1; }
	@set -eo pipefail; \
	if [ -f gh.env ]; then . ./gh.env; fi; \
	DIGEST=$$(cargo run --release --manifest-path tools/publisher/Cargo.toml --target $(HOST_TRIPLE) -- push \
	  --bin $(FW_BIN) \
	  --repo $(OCI_REPO) \
	  --app $(OTA_APP) \
	  --git-sha $(GIT_SHA) \
	  --source https://github.com/imjasonh/playground | grep '^digest:' | head -1 | cut -d' ' -f2); \
	test -n "$$DIGEST" || { echo "ERROR: publisher did not emit a 'digest:' line on stdout"; exit 1; }; \
	echo ">>> Signing $(OCI_REPO)@$$DIGEST with cosign (keyless OIDC)"; \
	COSIGN_REGISTRY_USERNAME=$(COSIGN_REGISTRY_USERNAME) COSIGN_REGISTRY_PASSWORD="$$GH_TOKEN" \
	  cosign sign --yes $(OCI_REPO)@$$DIGEST

pull-verify: SHELL := /bin/bash
pull-verify: $(INKBOT_FW_BIN) $(MAZE_FW_BIN) check-gh-env
	$(MAKE) pull-verify-one OCI_REPO=$(INKBOT_OCI_REPO) FW_BIN=$(INKBOT_FW_BIN)
	$(MAKE) pull-verify-one OCI_REPO=$(MAZE_OCI_REPO) FW_BIN=$(MAZE_FW_BIN)

pull-verify-one: SHELL := /bin/bash
pull-verify-one: check-gh-env
	@set -eo pipefail; \
	if [ -f gh.env ]; then . ./gh.env; fi; \
	cargo run --release --manifest-path tools/publisher/Cargo.toml --target $(HOST_TRIPLE) -- pull-verify \
	  --repo $(OCI_REPO) \
	  --tag latest \
	  --bin $(FW_BIN) \
	  --auth

check-gh-env:
	@if [ -z "$$GH_TOKEN" ] && [ ! -f gh.env ]; then \
	  echo "ERROR: set GH_TOKEN or create gh.env with:"; \
	  echo "  echo 'export GH_TOKEN=ghp_xxxxxxxx' > gh.env"; \
	  exit 1; \
	fi
