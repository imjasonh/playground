# mcu-lab — multi-board / multi-app build, flash, and monitor helpers.
#
# Boards and apps are declared separately in manifest.json.
#   - Flash a new board once over USB with the universal OTA+OTel base firmware:
#       make flash-all BOARD=waveshare-epd75 APP=base
#       make flash-all BOARD=xiao-esp32c3   APP=base
#   - Then send feature apps (maze, bench, ...) wirelessly via BLE OTA, or flash over USB:
#       make flash BOARD=waveshare-epd75 APP=maze
#
# All apps for the same BOARD share target/$(BOARD)/ so esp-idf-sys and std
# are compiled only once per board.

SHELL := /bin/bash

BOARD ?= xiao-esp32c3
APP ?= base
PROFILING ?= 0

PORT ?= $(firstword $(wildcard /dev/cu.usbmodem* /dev/cu.usbserial-* /dev/ttyACM* /dev/ttyUSB*))
ifeq ($(PORT),)
PORT := /dev/cu.usbmodem101
endif

COMPATIBLE_PAIRS := $(shell python3 -c 'import json; m = json.load(open("manifest.json")); print(" ".join(f"{b}:{a}" for b, bd in m["boards"].items() for a, ad in m["apps"].items() if set(ad["requires"]).issubset(bd["capabilities"])))')
BOARD_META = $(shell python3 -c 'import json, sys; m = json.load(open("manifest.json")); b = m["boards"].get(sys.argv[1]); print(b.get(sys.argv[2], "") if b else "")' "$(BOARD)" "$(1)")
APP_META = $(shell python3 -c 'import json, sys; m = json.load(open("manifest.json")); a = m["apps"].get(sys.argv[1]); print(a.get(sys.argv[2], "") if a else "")' "$(APP)" "$(1)")
COMPATIBLE := $(shell python3 -c 'import json, sys; m = json.load(open("manifest.json")); b = m["boards"].get(sys.argv[1]); a = m["apps"].get(sys.argv[2]); print("1" if (b and a and set(a["requires"]).issubset(b["capabilities"])) else "")' "$(BOARD)" "$(APP)")

TARGET := $(call BOARD_META,target)
MCU := $(call BOARD_META,chip)
SDKCONFIG_IN := $(call BOARD_META,sdkconfig)
EXTRA_COMPONENTS := $(call BOARD_META,extra_components)
FIRMWARE_ID_FILE := $(call APP_META,firmware_id_file)
FIRMWARE_ID_CONST := $(call APP_META,firmware_id_const)

ifneq ($(EXTRA_COMPONENTS),)
EXTRA_COMPONENTS_FILE := $(CURDIR)/target/$(BOARD)/extra_components.toml
EXTRA_COMPONENTS_ENV := ESP_IDF_SYS_EXTRA_COMPONENTS_FILE=$(EXTRA_COMPONENTS_FILE)
else
EXTRA_COMPONENTS_FILE :=
EXTRA_COMPONENTS_ENV :=
endif

ifeq ($(COMPATIBLE),)
$(error Incompatible or unknown BOARD='$(BOARD)' APP='$(APP)' — valid BOARD:APP pairs: $(COMPATIBLE_PAIRS))
endif

BIN_NAME := $(BOARD)-$(APP)
FIRMWARE_ID := $(shell awk -F'"' '/pub const $(FIRMWARE_ID_CONST)/ { print $$2; exit }' $(FIRMWARE_ID_FILE))

ifeq ($(PROFILING),1)
FIRMWARE_FEATURES := firmware,profiling
else
FIRMWARE_FEATURES := firmware
endif

# Always preserve DWARF line tables in the ELF so production crash coredumps
# symbolize cleanly; `espflash save-image` strips debug sections from the .bin.
PROFILE_CARGO_ENV := CARGO_PROFILE_RELEASE_STRIP=none CARGO_PROFILE_RELEASE_DEBUG=line-tables-only

override CARGO_TARGET_DIR := $(CURDIR)/target
export CARGO_TARGET_DIR

# Share one target dir per BOARD so esp-idf-sys and std compile only once per board.
FW_TARGET_DIR := $(CURDIR)/target/$(BOARD)
BIN := $(FW_TARGET_DIR)/$(TARGET)/release/$(BIN_NAME)
SDKCONFIG_DEFAULTS := $(FW_TARGET_DIR)/sdkconfig.defaults
SDKCONFIG := $(FW_TARGET_DIR)/sdkconfig

ESP_TOOLCHAIN := $(shell if rustup toolchain list 2>/dev/null | grep -q '^esp'; then echo esp; else echo nightly; fi)
PYTHON_SHIM   := $(CURDIR)/.embuild/python-shim

export PATH := $(PYTHON_SHIM):$(PATH)
export ESP_IDF_TOOLS_INSTALL_DIR := custom:$(CURDIR)/.embuild

.PHONY: help list-targets build build-app build-profile build-gzip-bench flash-gzip-bench \
	profile-gzip-bench check-firmware symbolize flash flash-all monitor run clean test \
	ensure-python-shim

help:
	@echo "Targets (compatible BOARD:APP pairs from manifest.json: $(COMPATIBLE_PAIRS)):"
	@echo "  make test                                        Host-side protocol and maze unit tests"
	@echo "  make list-targets                                Print all compatible BOARD:APP pairs"
	@echo "  make build                                       Cross-compile all compatible BOARD:APP pairs + standalone gzip-bench"
	@echo "  make build-app BOARD=<b> APP=<a>                 Cross-compile one board+app target"
	@echo "  make build-profile BOARD=<b> APP=<a>             Cross-compile with profiling + DWARF line tables"
	@echo "  make build-gzip-bench                            Cross-compile standalone 240 MHz no-BT ESP32 Mask-ROM gzip-bench"
	@echo "  make flash-gzip-bench                            Flash standalone gzip-bench over USB-C to $(PORT)"
	@echo "  make profile-gzip-bench                          Reset $(PORT), capture benchmarks + 2 kHz PC profiles, emit SVG flame chart"
	@echo "  make symbolize BOARD=<b> APP=<a> PC='0x...'      Resolve PC hotspot addresses against $(BIN)"
	@echo "  make flash-all BOARD=<b> APP=base                One-time USB erase + bootloader + partitions + base OTA app"
	@echo "  make flash BOARD=<b> APP=<a> [PROFILING=1]       Fast USB app-only flash"
	@echo "  make monitor                                     Serial monitor on $(PORT)"
	@echo "  make clean                                       cargo clean"

list-targets:
	@printf '%s\n' $(COMPATIBLE_PAIRS)

test:
	cargo test --lib --locked

$(SDKCONFIG_DEFAULTS): $(SDKCONFIG_IN) partitions.csv
	@mkdir -p $(FW_TARGET_DIR)
	@sed 's|@PROJECT_DIR@|$(CURDIR)|g' $(SDKCONFIG_IN) > $@

build:
	@for pair in $(COMPATIBLE_PAIRS); do \
	  b=$${pair%%:*}; a=$${pair#*:}; \
	  $(MAKE) --no-print-directory build-app BOARD=$$b APP=$$a PROFILING=$(PROFILING) || exit 1; \
	done
	@$(MAKE) --no-print-directory build-gzip-bench
	@$(MAKE) --no-print-directory build-gzip-bench-xiao

GZIP_BENCH_TARGET_DIR := $(CURDIR)/target/waveshare-epd75-nobt
GZIP_BENCH_BIN := $(GZIP_BENCH_TARGET_DIR)/xtensa-esp32-espidf/release/waveshare-epd75-gzip-bench
GZIP_BENCH_SDKCONFIG_DEFAULTS := $(GZIP_BENCH_TARGET_DIR)/sdkconfig.defaults
GZIP_BENCH_SDKCONFIG := $(GZIP_BENCH_TARGET_DIR)/sdkconfig

$(GZIP_BENCH_SDKCONFIG_DEFAULTS): sdkconfig.defaults.epd-nobt.in partitions.csv
	@mkdir -p $(GZIP_BENCH_TARGET_DIR)
	@sed 's|@PROJECT_DIR@|$(CURDIR)|g' sdkconfig.defaults.epd-nobt.in > $@

build-gzip-bench: ensure-python-shim $(GZIP_BENCH_SDKCONFIG_DEFAULTS)
	$(PROFILE_CARGO_ENV) \
	MCU=esp32 \
	CARGO_TARGET_DIR=$(GZIP_BENCH_TARGET_DIR) \
	ESP_IDF_SDKCONFIG_DEFAULTS=$(GZIP_BENCH_SDKCONFIG_DEFAULTS) \
	ESP_IDF_SDKCONFIG=$(GZIP_BENCH_SDKCONFIG) \
	  cargo +$(ESP_TOOLCHAIN) build --release \
	    --features standalone \
	    --bin waveshare-epd75-gzip-bench \
	    --target xtensa-esp32-espidf \
	    -Z build-std=std,panic_abort
	@echo "firmware waveshare-epd75-gzip-bench -> $(GZIP_BENCH_BIN) ($$(wc -c < "$(GZIP_BENCH_BIN)") bytes ELF)"

flash-gzip-bench: build-gzip-bench
	espflash flash --port $(PORT) --partition-table partitions.csv $(GZIP_BENCH_BIN)

profile-gzip-bench:
	python3 scripts/gzip-bench-profile.py --port $(PORT) --elf $(GZIP_BENCH_BIN) --svg docs/esp32-rom-miniz-flamegraph.svg

XIAO_GZIP_BENCH_TARGET_DIR := $(CURDIR)/target/xiao-esp32c3-nobt
XIAO_GZIP_BENCH_BIN := $(XIAO_GZIP_BENCH_TARGET_DIR)/riscv32imc-esp-espidf/release/xiao-esp32c3-gzip-bench
XIAO_GZIP_BENCH_SDKCONFIG_DEFAULTS := $(XIAO_GZIP_BENCH_TARGET_DIR)/sdkconfig.defaults
XIAO_GZIP_BENCH_SDKCONFIG := $(XIAO_GZIP_BENCH_TARGET_DIR)/sdkconfig

$(XIAO_GZIP_BENCH_SDKCONFIG_DEFAULTS): sdkconfig.defaults.xiao-nobt.in partitions.csv
	@mkdir -p $(XIAO_GZIP_BENCH_TARGET_DIR)
	@sed 's|@PROJECT_DIR@|$(CURDIR)|g' sdkconfig.defaults.xiao-nobt.in > $@

build-gzip-bench-xiao: ensure-python-shim $(XIAO_GZIP_BENCH_SDKCONFIG_DEFAULTS)
	$(PROFILE_CARGO_ENV) \
	MCU=esp32c3 \
	CARGO_TARGET_DIR=$(XIAO_GZIP_BENCH_TARGET_DIR) \
	ESP_IDF_SDKCONFIG_DEFAULTS=$(XIAO_GZIP_BENCH_SDKCONFIG_DEFAULTS) \
	ESP_IDF_SDKCONFIG=$(XIAO_GZIP_BENCH_SDKCONFIG) \
	  cargo +$(ESP_TOOLCHAIN) build --release \
	    --features standalone \
	    --bin xiao-esp32c3-gzip-bench \
	    --target riscv32imc-esp-espidf \
	    -Z build-std=std,panic_abort
	@echo "firmware xiao-esp32c3-gzip-bench -> $(XIAO_GZIP_BENCH_BIN) ($$(wc -c < "$(XIAO_GZIP_BENCH_BIN)") bytes ELF)"

flash-gzip-bench-xiao: build-gzip-bench-xiao
	espflash flash --port $(PORT) --partition-table partitions.csv $(XIAO_GZIP_BENCH_BIN)

ifneq ($(EXTRA_COMPONENTS),)
$(EXTRA_COMPONENTS_FILE): $(EXTRA_COMPONENTS) camera_bindings.h
	@mkdir -p $(FW_TARGET_DIR)
	@sed 's|@PROJECT_DIR@|$(CURDIR)|g' $(EXTRA_COMPONENTS) > $@
endif

build-app: ensure-python-shim $(SDKCONFIG_DEFAULTS) $(EXTRA_COMPONENTS_FILE)
	@if [ -z "$(FIRMWARE_ID)" ]; then \
	  echo "ERROR: could not read $(FIRMWARE_ID_CONST) from $(FIRMWARE_ID_FILE) for $(BIN_NAME)"; \
	  exit 1; \
	fi
	$(PROFILE_CARGO_ENV) \
	$(EXTRA_COMPONENTS_ENV) \
	MCU=$(MCU) \
	CARGO_TARGET_DIR=$(FW_TARGET_DIR) \
	ESP_IDF_SDKCONFIG_DEFAULTS=$(SDKCONFIG_DEFAULTS) \
	ESP_IDF_SDKCONFIG=$(SDKCONFIG) \
	  cargo +$(ESP_TOOLCHAIN) build --release \
	    --features $(FIRMWARE_FEATURES) \
	    --bin $(BIN_NAME) \
	    --target $(TARGET) \
	    -Z build-std=std,panic_abort
	@if [ "$(PROFILING)" = "0" ]; then \
	  $(EXTRA_COMPONENTS_ENV) \
	  MCU=$(MCU) \
	  CARGO_TARGET_DIR=$(FW_TARGET_DIR) \
	  ESP_IDF_SDKCONFIG_DEFAULTS=$(SDKCONFIG_DEFAULTS) \
	  ESP_IDF_SDKCONFIG=$(SDKCONFIG) \
	    cargo +$(ESP_TOOLCHAIN) check --release \
	      --features firmware,profiling \
	      --bin $(BIN_NAME) \
	      --target $(TARGET) \
	      -Z build-std=std,panic_abort; \
	fi
	@$(MAKE) --no-print-directory check-firmware BOARD=$(BOARD) APP=$(APP)

build-profile:
	@$(MAKE) --no-print-directory build-app BOARD=$(BOARD) APP=$(APP) PROFILING=1

symbolize:
	@if [ -z "$(PC)" ]; then echo "Usage: make symbolize BOARD=$(BOARD) APP=$(APP) PC='0x42001a40 0x400d1a40'"; exit 1; fi
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
	@echo "firmware $(BIN_NAME) ($(FIRMWARE_ID)) -> $(BIN) ($$(wc -c < "$(BIN)") bytes ELF)"

BOOTLOADER = $(firstword $(wildcard $(FW_TARGET_DIR)/$(TARGET)/release/build/esp-idf-sys-*/out/build/bootloader/bootloader.bin))

flash: build-app
	espflash flash --port $(PORT) --partition-table partitions.csv $(BIN)

flash-all: build-app
	@test -n "$(BOOTLOADER)" || { echo "ERROR: bootloader.bin not found under target/$(BOARD)."; exit 1; }
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
