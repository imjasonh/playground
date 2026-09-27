# knob: build and flash helpers for both MCUs.
#
# One-time host setup:
#   cargo install espup espflash ldproxy
#   espup install --targets esp32,esp32s3
#   curl -LsSf https://astral.sh/uv/install.sh | sh
#
# Then:
#   make test
#   make build
#   make flash-s3          # USB-C flipped toward the ESP32-S3
#   make flash-esp32       # USB-C flipped toward the ESP32-U4WDH
#
# `make build APPS=clock,tone` compiles only those example apps into the
# S3 image. The default is all ten. The companion image has no apps.

SHELL := /bin/bash

PORT ?= $(firstword $(wildcard /dev/cu.usbmodem* /dev/cu.usbserial-* /dev/ttyACM* /dev/ttyUSB*))
ifeq ($(PORT),)
PORT := /dev/cu.usbserial-0001
endif

APPS ?= dial,clock,pomodoro,spectrum,tone,sketch,haptics,battery,card,remote
comma := ,
S3_APP_FEATURES := $(shell printf '%s' "$(APPS)" | awk -F, 'BEGIN{n=0} {for(i=1;i<=NF;i++) if($$i!=""){printf "%s%s", (n?",":""), "app-" $$i; n++}}')
S3_FEATURES := firmware-s3$(if $(S3_APP_FEATURES),$(comma)$(S3_APP_FEATURES))
ESP32_FEATURES := firmware-esp32

S3_TARGET := xtensa-esp32s3-espidf
ESP32_TARGET := xtensa-esp32-espidf

override CARGO_TARGET_DIR := $(CURDIR)/target
export CARGO_TARGET_DIR

S3_DIR := $(CURDIR)/target/knob-s3
ESP32_DIR := $(CURDIR)/target/knob-esp32
S3_BIN := $(S3_DIR)/$(S3_TARGET)/release/knob-s3
ESP32_BIN := $(ESP32_DIR)/$(ESP32_TARGET)/release/knob-esp32
S3_SDKCONFIG_DEFAULTS := $(S3_DIR)/sdkconfig.defaults
ESP32_SDKCONFIG_DEFAULTS := $(ESP32_DIR)/sdkconfig.defaults
S3_SDKCONFIG := $(S3_DIR)/sdkconfig
ESP32_SDKCONFIG := $(ESP32_DIR)/sdkconfig
S3_ID := $(shell awk -F'"' '/pub const FIRMWARE_ID_S3/ { print $$2; exit }' src/ble.rs)
ESP32_ID := $(shell awk -F'"' '/pub const FIRMWARE_ID_ESP32/ { print $$2; exit }' src/ble.rs)

RUSTUP_HOME    := $(shell rustup show home 2>/dev/null)
LIBCLANG_PATH  := $(firstword $(wildcard \
	$(RUSTUP_HOME)/toolchains/esp/xtensa-esp32-elf-clang/*/esp-clang/lib \
	$(RUSTUP_HOME)/toolchains/esp/xtensa-esp32s3-elf-clang/*/esp-clang/lib))
XTENSA_GCC_BIN := $(firstword $(wildcard $(RUSTUP_HOME)/toolchains/esp/xtensa-esp-elf/*/xtensa-esp-elf/bin))
PYTHON_SHIM    := $(CURDIR)/.embuild/python-shim

export LIBCLANG_PATH
export PATH := $(PYTHON_SHIM):$(XTENSA_GCC_BIN):$(PATH)
export ESP_IDF_TOOLS_INSTALL_DIR := custom:$(CURDIR)/.embuild

.PHONY: help build build-s3 build-esp32 check-s3 check-esp32 \
	flash-s3 flash-esp32 flash-all-s3 flash-all-esp32 monitor clean test \
	ensure-python-shim

help:
	@echo "Targets:"
	@echo "  make test            Host unit tests, including a one-app feature build"
	@echo "  make build           Cross-compile knob-s3 and knob-esp32"
	@echo "  make build APPS=clock,tone"
	@echo "                       S3 image with only those example apps"
	@echo "  make flash-s3        Build + flash the S3 image to $(PORT)"
	@echo "  make flash-esp32     Build + flash the companion image to $(PORT)"
	@echo "  make flash-all-s3    Erase + bootloader + partition table + S3 app"
	@echo "  make flash-all-esp32 Erase + bootloader + partition table + companion app"
	@echo "  make monitor         Serial monitor on $(PORT)"

test:
	cargo test --lib --locked
	cargo test --lib --locked --no-default-features --features app-dial

$(S3_SDKCONFIG_DEFAULTS): sdkconfig.defaults.s3.in partitions-s3.csv
	@mkdir -p $(S3_DIR)
	@sed 's|@PROJECT_DIR@|$(CURDIR)|g' sdkconfig.defaults.s3.in > $@

$(ESP32_SDKCONFIG_DEFAULTS): sdkconfig.defaults.esp32.in partitions-esp32.csv
	@mkdir -p $(ESP32_DIR)
	@sed 's|@PROJECT_DIR@|$(CURDIR)|g' sdkconfig.defaults.esp32.in > $@

build:
	$(MAKE) build-s3
	$(MAKE) build-esp32

build-s3: ensure-python-shim $(S3_SDKCONFIG_DEFAULTS)
	@if [ -z "$(S3_ID)" ]; then echo "ERROR: missing FIRMWARE_ID_S3"; exit 1; fi
	CARGO_TARGET_DIR=$(S3_DIR) \
	ESP_IDF_SDKCONFIG_DEFAULTS=$(S3_SDKCONFIG_DEFAULTS) \
	ESP_IDF_SDKCONFIG=$(S3_SDKCONFIG) \
	  cargo +esp build --release \
	    --no-default-features \
	    --features $(S3_FEATURES) \
	    --bin knob-s3 \
	    --target $(S3_TARGET) \
	    -Z build-std=std,panic_abort
	@$(MAKE) --no-print-directory check-s3

build-esp32: ensure-python-shim $(ESP32_SDKCONFIG_DEFAULTS)
	@if [ -z "$(ESP32_ID)" ]; then echo "ERROR: missing FIRMWARE_ID_ESP32"; exit 1; fi
	CARGO_TARGET_DIR=$(ESP32_DIR) \
	ESP_IDF_SDKCONFIG_DEFAULTS=$(ESP32_SDKCONFIG_DEFAULTS) \
	ESP_IDF_SDKCONFIG=$(ESP32_SDKCONFIG) \
	  cargo +esp build --release \
	    --no-default-features \
	    --features $(ESP32_FEATURES) \
	    --bin knob-esp32 \
	    --target $(ESP32_TARGET) \
	    -Z build-std=std,panic_abort
	@$(MAKE) --no-print-directory check-esp32

# OTA slots from partitions-s3.csv (0x600000) and partitions-esp32.csv (0x180000).
SLOT_S3 := 6291456
SLOT_ESP32 := 1572864

check-s3:
	@test -f "$(S3_BIN)" || { echo "ERROR: missing $(S3_BIN)"; exit 1; }
	@grep -a -F -q "$(S3_ID)" "$(S3_BIN)" || { echo "ERROR: $(S3_BIN) missing $(S3_ID)"; exit 1; }
	@echo "firmware $(S3_ID) -> $(S3_BIN) ($$(wc -c < "$(S3_BIN)") bytes ELF) features=$(S3_FEATURES)"
	@$(call check_slot,$(XTENSA_GCC_BIN)/xtensa-esp32s3-elf-size,$(S3_BIN),$(SLOT_S3))

check-esp32:
	@test -f "$(ESP32_BIN)" || { echo "ERROR: missing $(ESP32_BIN)"; exit 1; }
	@grep -a -F -q "$(ESP32_ID)" "$(ESP32_BIN)" || { echo "ERROR: $(ESP32_BIN) missing $(ESP32_ID)"; exit 1; }
	@echo "firmware $(ESP32_ID) -> $(ESP32_BIN) ($$(wc -c < "$(ESP32_BIN)") bytes ELF)"
	@$(call check_slot,$(XTENSA_GCC_BIN)/xtensa-esp32-elf-size,$(ESP32_BIN),$(SLOT_ESP32))

# text+data is the flash image. Fail the build when it does not fit the inactive OTA slot.
define check_slot
	@tool=""; \
	for candidate in "$(1)" "$(XTENSA_GCC_BIN)/xtensa-esp-elf-size"; do \
	  if [ -x "$$candidate" ]; then tool="$$candidate"; break; fi; \
	done; \
	if [ -n "$$tool" ]; then \
	  flash=$$($$tool -d "$(2)" | awk 'NR==2 {print $$1+$$2}'); \
	  echo "flash image $$flash bytes, slot $(3) bytes"; \
	  if [ -z "$$flash" ] || [ "$$flash" -gt "$(3)" ]; then \
	    echo "ERROR: flash image exceeds OTA slot"; \
	    exit 1; \
	  fi; \
	else \
	  echo "size tool $(1) missing; ELF byte count is the upper bound"; \
	fi
endef

S3_BOOTLOADER := $(firstword $(wildcard $(S3_DIR)/$(S3_TARGET)/release/build/esp-idf-sys-*/out/build/bootloader/bootloader.bin))
ESP32_BOOTLOADER := $(firstword $(wildcard $(ESP32_DIR)/$(ESP32_TARGET)/release/build/esp-idf-sys-*/out/build/bootloader/bootloader.bin))

flash-s3: build-s3
	espflash flash --chip esp32s3 --port $(PORT) --partition-table partitions-s3.csv $(S3_BIN)

flash-esp32: build-esp32
	espflash flash --chip esp32 --port $(PORT) --partition-table partitions-esp32.csv $(ESP32_BIN)

flash-all-s3: build-s3
	@test -n "$(S3_BOOTLOADER)" || { echo "ERROR: S3 bootloader.bin not found. Run make build-s3 first."; exit 1; }
	espflash erase-flash --port $(PORT)
	espflash flash --chip esp32s3 --port $(PORT) \
	  --bootloader $(S3_BOOTLOADER) \
	  --partition-table partitions-s3.csv \
	  $(S3_BIN)

flash-all-esp32: build-esp32
	@test -n "$(ESP32_BOOTLOADER)" || { echo "ERROR: companion bootloader.bin not found. Run make build-esp32 first."; exit 1; }
	espflash erase-flash --port $(PORT)
	espflash flash --chip esp32 --port $(PORT) \
	  --bootloader $(ESP32_BOOTLOADER) \
	  --partition-table partitions-esp32.csv \
	  $(ESP32_BIN)

monitor:
	espflash monitor --port $(PORT)

clean:
	cargo clean
	rm -rf .embuild

ensure-python-shim:
	@command -v uv >/dev/null || { echo "ERROR: uv not installed (see README)."; exit 1; }
	@command -v cargo >/dev/null || { echo "ERROR: cargo not installed."; exit 1; }
	@rustup toolchain list | grep -q '^esp' || { echo "ERROR: esp toolchain missing. Run: espup install --targets esp32,esp32s3"; exit 1; }
	@mkdir -p "$(PYTHON_SHIM)"
	@rm -f "$(PYTHON_SHIM)/python" "$(PYTHON_SHIM)/python3"
	@uv python install 3.12 >/dev/null
	@PY=$$(uv python find --managed-python 3.12) && \
	    ln -sfn "$$PY" "$(PYTHON_SHIM)/python3" && \
	    ln -sfn "$$PY" "$(PYTHON_SHIM)/python"
