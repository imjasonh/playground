# mcu-lab — multi-MCU build / flash / monitor helpers.
#
# Supported APP targets:
#   xiao-esp32c3   Seeed Studio XIAO ESP32-C3 (RISC-V, BLE profiler + OTA)
#   epd-maze       Waveshare 7.5" e-Paper ESP32 Driver Board (Xtensa, maze + BLE OTA)
#
# Local commands:
#   make test                                # host protocol + maze unit tests
#   make build                               # cross-compile all firmware targets
#   make build-profile APP=xiao-esp32c3      # build profiling ELF with DWARF line tables
#   make build-profile APP=epd-maze          # build Waveshare ESP32 profiling ELF
#   make flash-all APP=epd-maze PROFILING=1  # one-time USB erase + bootloader + partitions + app
#   make flash APP=epd-maze PROFILING=1      # fast USB app-only flash
#   make monitor                             # serial monitor

SHELL := /bin/bash

APP ?= xiao-esp32c3
PROFILING ?= 0

PORT ?= $(firstword $(wildcard /dev/cu.usbmodem* /dev/cu.usbserial-* /dev/ttyACM* /dev/ttyUSB*))
ifeq ($(PORT),)
PORT := /dev/cu.usbmodem101
endif

ifeq ($(APP),xiao-esp32c3)
TARGET := riscv32imc-esp-espidf
MCU := esp32c3
SDKCONFIG_IN := sdkconfig.defaults.xiao.in
FIRMWARE_ID := $(shell awk -F'"' '/pub const FIRMWARE_ID/ { print $$2; exit }' src/protocol.rs)
else ifeq ($(APP),epd-maze)
TARGET := xtensa-esp32-espidf
MCU := esp32
SDKCONFIG_IN := sdkconfig.defaults.epd.in
FIRMWARE_ID := $(shell awk -F'"' '/pub const MAZE_FIRMWARE_ID/ { print $$2; exit }' src/maze/mod.rs)
else
$(error Unknown APP '$(APP)' — expected xiao-esp32c3 or epd-maze)
endif

ifeq ($(PROFILING),1)
FIRMWARE_FEATURES := firmware,profiling
PROFILE_CARGO_ENV := CARGO_PROFILE_RELEASE_STRIP=none CARGO_PROFILE_RELEASE_DEBUG=line-tables-only
else
FIRMWARE_FEATURES := firmware
PROFILE_CARGO_ENV :=
endif

override CARGO_TARGET_DIR := $(CURDIR)/target
export CARGO_TARGET_DIR

FW_TARGET_DIR := $(CURDIR)/target/$(APP)
BIN := $(FW_TARGET_DIR)/$(TARGET)/release/$(APP)
SDKCONFIG_DEFAULTS := $(FW_TARGET_DIR)/sdkconfig.defaults
SDKCONFIG := $(FW_TARGET_DIR)/sdkconfig

ESP_TOOLCHAIN := $(shell if rustup toolchain list 2>/dev/null | grep -q '^esp'; then echo esp; else echo nightly; fi)
PYTHON_SHIM   := $(CURDIR)/.embuild/python-shim

export PATH := $(PYTHON_SHIM):$(PATH)
export ESP_IDF_TOOLS_INSTALL_DIR := custom:$(CURDIR)/.embuild

.PHONY: help build build-app build-profile check-firmware symbolize flash flash-all monitor run clean test \
	ensure-python-shim

help:
	@echo "Targets:"
	@echo "  make test                               Host-side protocol and maze unit tests"
	@echo "  make build                              Cross-compile both xiao-esp32c3 and epd-maze"
	@echo "  make build-app APP=<app>                Cross-compile one app (xiao-esp32c3 | epd-maze)"
	@echo "  make build-profile APP=<app>            Cross-compile one app with profiling + DWARF line tables"
	@echo "  make symbolize APP=<app> PC='0x...'     Resolve PC hotspot addresses against $(BIN)"
	@echo "  make flash APP=<app> [PROFILING=1]      Build + flash app to $(PORT)"
	@echo "  make flash-all APP=<app> [PROFILING=1]  Erase + write bootloader, partition table, app"
	@echo "  make monitor                            Serial monitor on $(PORT)"
	@echo "  make clean                              cargo clean"

test:
	cargo test --lib --locked

$(SDKCONFIG_DEFAULTS): $(SDKCONFIG_IN) partitions.csv
	@mkdir -p $(FW_TARGET_DIR)
	@sed 's|@PROJECT_DIR@|$(CURDIR)|g' $(SDKCONFIG_IN) > $@

build:
	@$(MAKE) --no-print-directory build-app APP=xiao-esp32c3 PROFILING=$(PROFILING)
	@$(MAKE) --no-print-directory build-app APP=epd-maze PROFILING=$(PROFILING)

build-app: ensure-python-shim $(SDKCONFIG_DEFAULTS)
	@if [ -z "$(FIRMWARE_ID)" ]; then \
	  echo "ERROR: could not read FIRMWARE_ID for $(APP)"; \
	  exit 1; \
	fi
	$(PROFILE_CARGO_ENV) \
	MCU=$(MCU) \
	CARGO_TARGET_DIR=$(FW_TARGET_DIR) \
	ESP_IDF_SDKCONFIG_DEFAULTS=$(SDKCONFIG_DEFAULTS) \
	ESP_IDF_SDKCONFIG=$(SDKCONFIG) \
	  cargo +$(ESP_TOOLCHAIN) build --release \
	    --features $(FIRMWARE_FEATURES) \
	    --bin $(APP) \
	    --target $(TARGET) \
	    -Z build-std=std,panic_abort
	@if [ "$(PROFILING)" = "0" ]; then \
	  MCU=$(MCU) \
	  CARGO_TARGET_DIR=$(FW_TARGET_DIR) \
	  ESP_IDF_SDKCONFIG_DEFAULTS=$(SDKCONFIG_DEFAULTS) \
	  ESP_IDF_SDKCONFIG=$(SDKCONFIG) \
	    cargo +$(ESP_TOOLCHAIN) check --release \
	      --features firmware,profiling \
	      --bin $(APP) \
	      --target $(TARGET) \
	      -Z build-std=std,panic_abort; \
	fi
	@$(MAKE) --no-print-directory check-firmware APP=$(APP)

build-profile:
	@$(MAKE) --no-print-directory build-app APP=$(APP) PROFILING=1

symbolize:
	@if [ -z "$(PC)" ]; then echo "Usage: make symbolize APP=$(APP) PC='0x42001a40 0x400d1a40'"; exit 1; fi
	@if command -v llvm-symbolizer >/dev/null 2>&1; then \
	  llvm-symbolizer -e "$(BIN)" --demangle $(PC); \
	elif command -v riscv32-esp-elf-addr2line >/dev/null 2>&1; then \
	  riscv32-esp-elf-addr2line -f -C -i -e "$(BIN)" $(PC); \
	else \
	  addr2line -f -C -i -e "$(BIN)" $(PC); \
	fi

check-firmware:
	@if [ ! -f "$(BIN)" ]; then echo "ERROR: missing $(BIN)"; exit 1; fi
	@if ! grep -a -F -q "$(FIRMWARE_ID)" "$(BIN)"; then \
	  echo "ERROR: $(BIN) does not contain $(FIRMWARE_ID) (stale ELF?)"; \
	  exit 1; \
	fi
	@echo "firmware $(APP) ($(FIRMWARE_ID)) -> $(BIN) ($$(wc -c < "$(BIN)") bytes ELF)"

BOOTLOADER = $(firstword $(wildcard $(FW_TARGET_DIR)/$(TARGET)/release/build/esp-idf-sys-*/out/build/bootloader/bootloader.bin))

flash: build-app
	espflash flash --port $(PORT) --partition-table partitions.csv $(BIN)

flash-all: build-app
	@test -n "$(BOOTLOADER)" || { echo "ERROR: bootloader.bin not found under target/$(APP)."; exit 1; }
	espflash erase-flash --port $(PORT)
	espflash flash --port $(PORT) --bootloader $(BOOTLOADER) --partition-table partitions.csv $(BIN)

monitor:
	espflash monitor --port $(PORT)

run: flash monitor

clean:
	cargo clean
	rm -rf .embuild

ensure-python-shim:
	@command -v uv >/dev/null || { echo "ERROR: uv not installed (see README)."; exit 1; }
	@command -v cargo >/dev/null || { echo "ERROR: cargo not installed."; exit 1; }
	@if [ "$(ESP_TOOLCHAIN)" = "nightly" ] && ! rustup toolchain list 2>/dev/null | grep -q '^nightly'; then \
	  rustup toolchain install nightly --profile minimal --no-self-update --component rust-src; \
	fi
	@mkdir -p "$(PYTHON_SHIM)"
	@rm -f "$(PYTHON_SHIM)/python" "$(PYTHON_SHIM)/python3"
	@uv python install 3.12 >/dev/null
	@PY=$$(uv python find --managed-python 3.12) && \
	    ln -sfn "$$PY" "$(PYTHON_SHIM)/python3" && \
	    ln -sfn "$$PY" "$(PYTHON_SHIM)/python"
