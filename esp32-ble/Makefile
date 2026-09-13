# esp32-ble — build / flash / monitor helpers.
#
# One-time host setup (same as inkbot-esp32):
#   cargo install espup espflash ldproxy
#   brew install cmake ninja dfu-util   # or apt-get install cmake ninja-build
#   espup install --targets esp32
#   curl -LsSf https://astral.sh/uv/install.sh | sh
#
# Then:
#   make test
#   make flash
#   make monitor

SHELL := /bin/bash

PORT ?= $(firstword $(wildcard /dev/cu.usbmodem* /dev/cu.usbserial-* /dev/ttyACM* /dev/ttyUSB*))
ifeq ($(PORT),)
PORT := /dev/cu.usbserial-0001
endif
TARGET := xtensa-esp32-espidf
FIRMWARE_FEATURES := firmware

override CARGO_TARGET_DIR := $(CURDIR)/target
export CARGO_TARGET_DIR

FW_TARGET_DIR := $(CURDIR)/target/esp32-ble
BIN := $(FW_TARGET_DIR)/$(TARGET)/release/esp32-ble
SDKCONFIG_DEFAULTS := $(FW_TARGET_DIR)/sdkconfig.defaults
SDKCONFIG := $(FW_TARGET_DIR)/sdkconfig
FIRMWARE_ID := $(shell awk -F'"' '/pub const FIRMWARE_ID/ { print $$2; exit }' src/protocol.rs)

RUSTUP_HOME    := $(shell rustup show home 2>/dev/null)
LIBCLANG_PATH  := $(firstword $(wildcard $(RUSTUP_HOME)/toolchains/esp/xtensa-esp32-elf-clang/*/esp-clang/lib))
XTENSA_GCC_BIN := $(firstword $(wildcard $(RUSTUP_HOME)/toolchains/esp/xtensa-esp-elf/*/xtensa-esp-elf/bin))
PYTHON_SHIM    := $(CURDIR)/.embuild/python-shim

export LIBCLANG_PATH
export PATH := $(PYTHON_SHIM):$(XTENSA_GCC_BIN):$(PATH)
export ESP_IDF_TOOLS_INSTALL_DIR := custom:$(CURDIR)/.embuild

.PHONY: help build check-firmware flash flash-all monitor run clean test \
	ensure-python-shim

help:
	@echo "Targets:"
	@echo "  make test      Host-side protocol unit tests"
	@echo "  make build     Cross-compile $(FIRMWARE_ID) (needs espup)"
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
	  cargo +esp build --release \
	    --features $(FIRMWARE_FEATURES) \
	    --bin esp32-ble \
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
	@rustup toolchain list | grep -q '^esp' || { echo "ERROR: esp toolchain missing. Run: espup install --targets esp32"; exit 1; }
	@mkdir -p "$(PYTHON_SHIM)"
	@rm -f "$(PYTHON_SHIM)/python" "$(PYTHON_SHIM)/python3"
	@uv python install 3.12 >/dev/null
	@PY=$$(uv python find --managed-python 3.12) && \
	    ln -sfn "$$PY" "$(PYTHON_SHIM)/python3" && \
	    ln -sfn "$$PY" "$(PYTHON_SHIM)/python"
