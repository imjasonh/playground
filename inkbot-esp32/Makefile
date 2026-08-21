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

SHELL := /bin/bash

PORT ?= $(firstword $(wildcard /dev/cu.usbmodem* /dev/cu.usbserial-*))
ifeq ($(PORT),)
PORT := /dev/cu.usbserial-0001
endif
TARGET := xtensa-esp32-espidf
APP ?= inkbot
HOST_TRIPLE := $(shell rustc -vV | sed -n 's/^host: //p')

override CARGO_TARGET_DIR := $(CURDIR)/target
export CARGO_TARGET_DIR

INKBOT_BIN := $(CARGO_TARGET_DIR)/$(TARGET)/release/inkbot-esp32
MAZE_BIN := $(CARGO_TARGET_DIR)/$(TARGET)/release/maze-esp32
FW_BIN := $(CARGO_TARGET_DIR)/firmware.bin
NVS_BIN := $(CARGO_TARGET_DIR)/nvs.bin
INKBOT_FIRMWARE_ID := $(shell awk -F'"' '/pub const FIRMWARE_ID/ { print $$2; exit }' src/status.rs)
MAZE_FIRMWARE_ID := $(shell awk -F'"' '/MAZE_FIRMWARE_ID/ { print $$2; exit }' src/maze/mod.rs)

ifeq ($(APP),maze)
BIN := $(MAZE_BIN)
FIRMWARE_ID := $(MAZE_FIRMWARE_ID)
else
BIN := $(INKBOT_BIN)
FIRMWARE_ID := $(INKBOT_FIRMWARE_ID)
endif

OCI_REPO ?= ghcr.io/imjasonh/playground/inkbot-esp32
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
export ESP_IDF_SDKCONFIG_DEFAULTS := $(CURDIR)/sdkconfig.defaults

BOOTLOADER := $(firstword $(wildcard $(CARGO_TARGET_DIR)/$(TARGET)/release/build/esp-idf-sys-*/out/build/bootloader/bootloader.bin))
NVS_GEN_PY := $(CURDIR)/.embuild/espressif/esp-idf/v5.2.2/components/nvs_flash/nvs_partition_generator/nvs_partition_gen.py
NVS_GEN_PYTHON := $(CURDIR)/.embuild/espressif/python_env/idf5.2_py3.12_env/bin/python

.PHONY: help build check-firmware flash flash-all monitor run clean test \
	ensure-python-shim sdkconfig.defaults save-image publish pull-verify \
	provision provision-build bootstrap check-gh-env

help:
	@echo "Targets:"
	@echo "  make build          Cross-compile inkbot + maze firmware"
	@echo "  make flash          Build + flash $(FIRMWARE_ID) to $(PORT) (APP=$(APP))"
	@echo "  make flash APP=maze Flash the maze firmware (same OTA partition table)"
	@echo "  make flash-all      Erase + write bootloader, partition table, app"
	@echo "  make provision      Write NVS from provisioning.toml"
	@echo "  make bootstrap      flash-all + provision"
	@echo "  make publish        Push signed firmware to $(OCI_REPO)"
	@echo "  make monitor        Serial monitor on $(PORT)"
	@echo "  make test           Host-side unit tests + provision dry-run"
	@echo "  make clean          cargo clean"

test:
	cargo test --lib --locked
	cargo run --manifest-path tools/provision/Cargo.toml --locked -- \
	  --config $(CURDIR)/provisioning.toml.example \
	  --out $(CURDIR)/target/nvs-dry.bin \
	  --dry-run

sdkconfig.defaults: sdkconfig.defaults.in partitions.csv
	@sed 's|@PROJECT_DIR@|$(CURDIR)|g' sdkconfig.defaults.in > sdkconfig.defaults

build: ensure-python-shim sdkconfig.defaults
	@if [ -z "$(INKBOT_FIRMWARE_ID)" ]; then \
	  echo "ERROR: could not read FIRMWARE_ID from src/status.rs"; \
	  exit 1; \
	fi
	@if [ -z "$(MAZE_FIRMWARE_ID)" ]; then \
	  echo "ERROR: could not read MAZE_FIRMWARE_ID from src/maze/mod.rs"; \
	  exit 1; \
	fi
	ESP_IDF_SDKCONFIG_DEFAULTS=$(ESP_IDF_SDKCONFIG_DEFAULTS) \
	  cargo +esp build --release --features firmware \
	    --bin inkbot-esp32 --bin maze-esp32 \
	    --target $(TARGET) \
	    -Z build-std=std,panic_abort
	@$(MAKE) --no-print-directory check-firmware

check-firmware:
	@if [ ! -f "$(INKBOT_BIN)" ]; then echo "ERROR: missing $(INKBOT_BIN)"; exit 1; fi
	@if [ ! -f "$(MAZE_BIN)" ]; then echo "ERROR: missing $(MAZE_BIN)"; exit 1; fi
	@if ! grep -a -F -q "$(INKBOT_FIRMWARE_ID)" "$(INKBOT_BIN)"; then \
	  echo "ERROR: $(INKBOT_BIN) does not contain $(INKBOT_FIRMWARE_ID) (stale ELF?)"; \
	  exit 1; \
	fi
	@if ! grep -a -F -q "$(MAZE_FIRMWARE_ID)" "$(MAZE_BIN)"; then \
	  echo "ERROR: $(MAZE_BIN) does not contain $(MAZE_FIRMWARE_ID) (stale ELF?)"; \
	  exit 1; \
	fi
	@echo "firmware $(INKBOT_FIRMWARE_ID) -> $(INKBOT_BIN) ($$(wc -c < "$(INKBOT_BIN)") bytes ELF)"
	@echo "firmware $(MAZE_FIRMWARE_ID) -> $(MAZE_BIN) ($$(wc -c < "$(MAZE_BIN)") bytes ELF)"
	@echo "flash APP=$(APP) -> $(BIN) ($(FIRMWARE_ID))"

# Always pass the OTA partition table. Without it, espflash 4.x writes a
# factory-only table and the next OTA poll cannot find a second slot.
flash: build
	espflash flash --port $(PORT) --partition-table partitions.csv $(BIN)

flash-all: build
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

provision: provisioning.toml build
	cargo run --release --manifest-path tools/provision/Cargo.toml --target $(HOST_TRIPLE) -- \
	  --config $(CURDIR)/provisioning.toml \
	  --out $(CURDIR)/$(NVS_BIN) \
	  --nvs-gen $(NVS_GEN_PY) \
	  --python $(NVS_GEN_PYTHON) \
	  --port $(PORT) \
	  --flash

provision-build: provisioning.toml build
	cargo run --release --manifest-path tools/provision/Cargo.toml --target $(HOST_TRIPLE) -- \
	  --config $(CURDIR)/provisioning.toml \
	  --out $(CURDIR)/$(NVS_BIN) \
	  --nvs-gen $(NVS_GEN_PY) \
	  --python $(NVS_GEN_PYTHON)

bootstrap: flash-all provision

save-image: $(FW_BIN)

$(FW_BIN): build
	espflash save-image --chip esp32 --partition-table partitions.csv $(INKBOT_BIN) $(FW_BIN)
	@echo "Wrote $(FW_BIN) ($$(wc -c < $(FW_BIN)) bytes)"

publish: SHELL := /bin/bash
publish: $(FW_BIN) check-gh-env
	@set -eo pipefail; \
	if [ -f gh.env ]; then . ./gh.env; fi; \
	DIGEST=$$(cargo run --release --manifest-path tools/publisher/Cargo.toml --target $(HOST_TRIPLE) -- push \
	  --bin $(CURDIR)/$(FW_BIN) \
	  --repo $(OCI_REPO) \
	  --git-sha $(GIT_SHA) \
	  --source https://github.com/imjasonh/playground | grep '^digest:' | head -1 | cut -d' ' -f2); \
	test -n "$$DIGEST" || { echo "ERROR: publisher did not emit a 'digest:' line on stdout"; exit 1; }; \
	echo ">>> Signing $(OCI_REPO)@$$DIGEST with cosign (keyless OIDC)"; \
	COSIGN_REGISTRY_USERNAME=$(COSIGN_REGISTRY_USERNAME) COSIGN_REGISTRY_PASSWORD="$$GH_TOKEN" \
	  cosign sign --yes $(OCI_REPO)@$$DIGEST

pull-verify: $(FW_BIN) check-gh-env
	@set -eo pipefail; \
	if [ -f gh.env ]; then . ./gh.env; fi; \
	cargo run --release --manifest-path tools/publisher/Cargo.toml --target $(HOST_TRIPLE) -- pull-verify \
	  --repo $(OCI_REPO) \
	  --tag latest \
	  --bin $(CURDIR)/$(FW_BIN) \
	  --auth

check-gh-env:
	@if [ -z "$$GH_TOKEN" ] && [ ! -f gh.env ]; then \
	  echo "ERROR: set GH_TOKEN or create gh.env with:"; \
	  echo "  echo 'export GH_TOKEN=ghp_xxxxxxxx' > gh.env"; \
	  exit 1; \
	fi
