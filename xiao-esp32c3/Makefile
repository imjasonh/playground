# xiao-esp32c3 — build / flash / monitor helpers.
#
# One-time host setup:
#   cargo install espflash ldproxy
#   brew install cmake ninja dfu-util   # or apt-get install cmake ninja-build
#   rustup toolchain install nightly --component rust-src
#   curl -LsSf https://astral.sh/uv/install.sh | sh
#
# Then:
#   make test
#   make flash
#   make monitor

SHELL := /bin/bash

PORT ?= $(firstword $(wildcard /dev/cu.usbmodem* /dev/cu.usbserial-* /dev/ttyACM* /dev/ttyUSB*))
ifeq ($(PORT),)
PORT := /dev/cu.usbmodem101
endif
TARGET := riscv32imc-esp-espidf
FIRMWARE_FEATURES := firmware

override CARGO_TARGET_DIR := $(CURDIR)/target
export CARGO_TARGET_DIR

FW_TARGET_DIR := $(CURDIR)/target/xiao-esp32c3
BIN := $(FW_TARGET_DIR)/$(TARGET)/release/xiao-esp32c3
SDKCONFIG_DEFAULTS := $(FW_TARGET_DIR)/sdkconfig.defaults
SDKCONFIG := $(FW_TARGET_DIR)/sdkconfig
FIRMWARE_ID := $(shell awk -F'"' '/pub const FIRMWARE_ID/ { print $$2; exit }' src/protocol.rs)

# Prefer `cargo +esp` when installed via espup; fall back to `cargo +nightly`
# since `riscv32imc-esp-espidf` is a tier-3 target in upstream Rust.
ESP_TOOLCHAIN := $(shell if rustup toolchain list 2>/dev/null | grep -q '^esp'; then echo esp; else echo nightly; fi)
PYTHON_SHIM   := $(CURDIR)/.embuild/python-shim

export PATH := $(PYTHON_SHIM):$(PATH)
export ESP_IDF_TOOLS_INSTALL_DIR := custom:$(CURDIR)/.embuild

.PHONY: help build check-firmware flash flash-all monitor run clean test \
	ensure-python-shim

help:
	@echo "Targets:"
	@echo "  make test      Host-side protocol and OTLP unit tests"
	@echo "  make build     Cross-compile $(FIRMWARE_ID) for $(TARGET)"
	@echo "  make flash     Build + flash to $(PORT)"
	@echo "  make flash-all Erase + write bootloader, partition table, app"
	@echo "  make monitor   Serial monitor on $(PORT)"
	@echo "  make clean     cargo clean"

test:
	cargo test --lib --locked

$(SDKCONFIG_DEFAULTS): sdkconfig.defaults.in
	@mkdir -p $(FW_TARGET_DIR)
	@sed 's|@PROJECT_DIR@|$(CURDIR)|g' sdkconfig.defaults.in > $@

build: ensure-python-shim $(SDKCONFIG_DEFAULTS)
	@if [ -z "$(FIRMWARE_ID)" ]; then \
	  echo "ERROR: could not read FIRMWARE_ID from src/protocol.rs"; \
	  exit 1; \
	fi
	CARGO_TARGET_DIR=$(FW_TARGET_DIR) \
	ESP_IDF_SDKCONFIG_DEFAULTS=$(SDKCONFIG_DEFAULTS) \
	ESP_IDF_SDKCONFIG=$(SDKCONFIG) \
	  cargo +$(ESP_TOOLCHAIN) build --release \
	    --features $(FIRMWARE_FEATURES) \
	    --bin xiao-esp32c3 \
	    --target $(TARGET) \
	    -Z build-std=std,panic_abort
	@$(MAKE) --no-print-directory check-firmware

check-firmware:
	@if [ ! -f "$(BIN)" ]; then echo "ERROR: missing $(BIN)"; exit 1; fi
	@if ! grep -a -F -q "$(FIRMWARE_ID)" "$(BIN)"; then \
	  echo "ERROR: $(BIN) does not contain $(FIRMWARE_ID) (stale ELF?)"; \
	  exit 1; \
	fi
	@echo "firmware $(FIRMWARE_ID) -> $(BIN) ($$(wc -c < "$(BIN)") bytes ELF)"

BOOTLOADER := $(firstword $(wildcard $(FW_TARGET_DIR)/$(TARGET)/release/build/esp-idf-sys-*/out/build/bootloader/bootloader.bin))

flash: build
	espflash flash --port $(PORT) $(BIN)

flash-all: build
	@test -n "$(BOOTLOADER)" || { echo "ERROR: bootloader.bin not found under target/. Run 'make build' first."; exit 1; }
	espflash erase-flash --port $(PORT)
	espflash flash --port $(PORT) --bootloader $(BOOTLOADER) $(BIN)

monitor:
	espflash monitor --port $(PORT)

run: flash monitor

clean:
	cargo clean
	rm -rf .embuild sdkconfig.defaults

ensure-python-shim:
	@command -v uv >/dev/null || { echo "ERROR: uv not installed (see README)."; exit 1; }
	@command -v cargo >/dev/null || { echo "ERROR: cargo not installed."; exit 1; }
	@if [ "$(ESP_TOOLCHAIN)" = "nightly" ] && ! rustup toolchain list | grep -q '^nightly'; then \
	  rustup toolchain install nightly --profile minimal --no-self-update --component rust-src; \
	fi
	@mkdir -p "$(PYTHON_SHIM)"
	@rm -f "$(PYTHON_SHIM)/python" "$(PYTHON_SHIM)/python3"
	@uv python install 3.12 >/dev/null
	@PY=$$(uv python find --managed-python 3.12) && \
	    ln -sfn "$$PY" "$(PYTHON_SHIM)/python3" && \
	    ln -sfn "$$PY" "$(PYTHON_SHIM)/python"
