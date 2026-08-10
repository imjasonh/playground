# inkbot-esp32 — build / flash / monitor helpers.
#
# One-time host setup (macOS):
#   cargo install espup espflash ldproxy
#   brew install cmake ninja dfu-util
#   espup install --targets esp32
#   curl -LsSf https://astral.sh/uv/install.sh | sh
#
# Then:
#   cp config.toml.example config.toml   # Wi-Fi + Worker URL
#   make build
#   make flash
#   make monitor

PORT ?= /dev/cu.usbserial-0001
TARGET := xtensa-esp32-espidf
BIN := target/$(TARGET)/release/inkbot-esp32

RUSTUP_HOME    := $(shell rustup show home 2>/dev/null)
LIBCLANG_PATH  := $(firstword $(wildcard $(RUSTUP_HOME)/toolchains/esp/xtensa-esp32-elf-clang/*/esp-clang/lib))
XTENSA_GCC_BIN := $(firstword $(wildcard $(RUSTUP_HOME)/toolchains/esp/xtensa-esp-elf/*/xtensa-esp-elf/bin))
PYTHON_SHIM    := $(CURDIR)/.embuild/python-shim

export LIBCLANG_PATH
export PATH := $(PYTHON_SHIM):$(XTENSA_GCC_BIN):$(PATH)
export ESP_IDF_TOOLS_INSTALL_DIR := custom:$(CURDIR)/.embuild
export ESP_IDF_SDKCONFIG_DEFAULTS := $(CURDIR)/sdkconfig.defaults

.PHONY: help build flash monitor run clean test ensure-python-shim

help:
	@echo "Targets:"
	@echo "  make build     Cross-compile firmware (espup toolchain)"
	@echo "  make flash     Build + flash app to $(PORT)"
	@echo "  make monitor   Serial monitor on $(PORT)"
	@echo "  make run       Build + flash + monitor"
	@echo "  make test      Host-side unit tests (no ESP toolchain needed)"
	@echo "  make clean     cargo clean"

test:
	cargo test --lib

build: ensure-python-shim
	ESP_IDF_SDKCONFIG_DEFAULTS=$(ESP_IDF_SDKCONFIG_DEFAULTS) \
	  cargo +esp build --release --features firmware \
	    --target $(TARGET) \
	    -Z build-std=std,panic_abort

flash: build
	espflash flash --port $(PORT) $(BIN)

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
	@rm -rf $(PYTHON_SHIM)
	@mkdir -p $(PYTHON_SHIM)
	@UV_PY=$$(uv python find 3.12) || { uv python install 3.12; UV_PY=$$(uv python find 3.12); }
	@ln -sf "$$UV_PY" $(PYTHON_SHIM)/python3
	@ln -sf "$$UV_PY" $(PYTHON_SHIM)/python
