# inkbot-esp32 — build / flash / monitor helpers.
#
# One-time host setup (macOS):
#   cargo install espup espflash ldproxy
#   brew install cmake ninja dfu-util
#   espup install --targets esp32
#   curl -LsSf https://astral.sh/uv/install.sh | sh
#
# Then:
#   cp nvs/device.csv.example nvs/device.csv   # Wi-Fi + Worker URL (inkbot)
#   make build                           # both inkbot-esp32 and maze-esp32
#   make flash                           # APP=inkbot (default)
#   make flash APP=maze
#   make monitor

# Ubuntu CI's /bin/sh is dash, which rejects `set -o pipefail`.
SHELL := /bin/bash

PORT ?= $(firstword $(wildcard /dev/cu.usbmodem* /dev/cu.usbserial-*))
ifeq ($(PORT),)
PORT := /dev/cu.usbserial-0001
endif
TARGET := xtensa-esp32-espidf
APP ?= inkbot

# Cursor/agent shells often export CARGO_TARGET_DIR into a sandbox cache.
# cargo then writes the ESP ELF there while `make flash` still uploaded
# inkbot-esp32/target/... — a stale image, so the panel kept reporting
# inkbot-esp32/0.1 after we thought we had flashed 0.2. Pin every
# Make-driven cargo invocation to this crate.
override CARGO_TARGET_DIR := $(CURDIR)/target
export CARGO_TARGET_DIR

INKBOT_BIN := $(CARGO_TARGET_DIR)/$(TARGET)/release/inkbot-esp32
MAZE_BIN := $(CARGO_TARGET_DIR)/$(TARGET)/release/maze-esp32
INKBOT_FIRMWARE_ID := $(shell awk -F'"' '/pub const FIRMWARE_ID/ { print $$2; exit }' src/status.rs)
MAZE_FIRMWARE_ID := $(shell awk -F'"' '/MAZE_FIRMWARE_ID/ { print $$2; exit }' src/maze/mod.rs)

ifeq ($(APP),maze)
BIN := $(MAZE_BIN)
FIRMWARE_ID := $(MAZE_FIRMWARE_ID)
else
BIN := $(INKBOT_BIN)
FIRMWARE_ID := $(INKBOT_FIRMWARE_ID)
endif

RUSTUP_HOME    := $(shell rustup show home 2>/dev/null)
LIBCLANG_PATH  := $(firstword $(wildcard $(RUSTUP_HOME)/toolchains/esp/xtensa-esp32-elf-clang/*/esp-clang/lib))
XTENSA_GCC_BIN := $(firstword $(wildcard $(RUSTUP_HOME)/toolchains/esp/xtensa-esp-elf/*/xtensa-esp-elf/bin))
PYTHON_SHIM    := $(CURDIR)/.embuild/python-shim

export LIBCLANG_PATH
export PATH := $(PYTHON_SHIM):$(XTENSA_GCC_BIN):$(PATH)
export ESP_IDF_TOOLS_INSTALL_DIR := custom:$(CURDIR)/.embuild
export ESP_IDF_SDKCONFIG_DEFAULTS := $(CURDIR)/sdkconfig.defaults

.PHONY: help build check-firmware flash monitor run clean test ensure-python-shim nvs

help:
	@echo "Targets:"
	@echo "  make build          Cross-compile inkbot + maze firmware (espup toolchain)"
	@echo "  make flash          Build + flash $(FIRMWARE_ID) to $(PORT) (APP=$(APP))"
	@echo "  make flash APP=maze Flash the maze firmware (no Wi-Fi)"
	@echo "  make nvs            Flash device config from nvs/device.csv (no rebuild)"
	@echo "  make monitor        Serial monitor on $(PORT)"
	@echo "  make run            Build + flash + monitor"
	@echo "  make test           Host-side unit tests (no ESP toolchain needed)"
	@echo "  make clean          cargo clean"

test:
	cargo test --lib --locked

build: ensure-python-shim
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

# Refuse to flash (or CI-ship) an ELF whose baked id doesn't match source —
# the usual symptom of a CARGO_TARGET_DIR mismatch.
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
	@echo "firmware $(INKBOT_FIRMWARE_ID) -> $(INKBOT_BIN)"
	@echo "firmware $(MAZE_FIRMWARE_ID) -> $(MAZE_BIN)"
	@echo "flash APP=$(APP) -> $(BIN) ($(FIRMWARE_ID))"

flash: build
	espflash flash --port $(PORT) $(BIN)

# Flash Wi-Fi / Worker / Sigstore pins without rebuilding the app ELF.
# Requires nvs/device.csv (from nvs/device.csv.example) and a prior
# `make build` so ESP-IDF's nvs_partition_gen.py is available under .embuild.
# Replaces the entire NVS partition (clears catalog bookmarks).
NVS_CSV ?= $(CURDIR)/nvs/device.csv
NVS_BIN ?= $(CURDIR)/nvs/device.bin
# Default single-app table: nvs at 0x9000, size 0x6000.
NVS_OFFSET ?= 0x9000
NVS_SIZE ?= 0x6000
NVS_GEN := $(firstword $(wildcard $(CURDIR)/.embuild/espressif/esp-idf/*/components/nvs_flash/nvs_partition_generator/nvs_partition_gen.py))

nvs: ensure-python-shim
	@if [ ! -f "$(NVS_CSV)" ]; then \
	  echo "ERROR: missing $(NVS_CSV)"; \
	  echo "  cp nvs/device.csv.example nvs/device.csv  # then edit ssid / base_url"; \
	  exit 1; \
	fi
	@if [ -z "$(NVS_GEN)" ]; then \
	  echo "ERROR: nvs_partition_gen.py not found under .embuild/"; \
	  echo "  Run: make build   # once, to fetch ESP-IDF"; \
	  exit 1; \
	fi
	$(PYTHON_SHIM)/python "$(NVS_GEN)" generate "$(NVS_CSV)" "$(NVS_BIN)" $(NVS_SIZE)
	espflash write-bin --port $(PORT) $(NVS_OFFSET) "$(NVS_BIN)"
	@echo "flashed device NVS from $(NVS_CSV) -> $(NVS_OFFSET)"

monitor:
	espflash monitor --port $(PORT)

run: flash monitor

clean:
	cargo clean
	rm -rf .embuild

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
