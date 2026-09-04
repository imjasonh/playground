# Host tests always. Cross-build the G071 image when arm-none-eabi-gcc exists.
CC ?= cc
CFLAGS ?= -std=c11 -Wall -Wextra -Werror -Iinclude
HOST_BIN = host/test_protocol host/test_image host/pack_pbm

.PHONY: all test clean mcu

all: test

host/test_protocol: host/test_protocol.c src/protocol.c
	$(CC) $(CFLAGS) -o $@ host/test_protocol.c src/protocol.c

host/test_image: host/test_image.c src/image.c src/protocol.c
	$(CC) $(CFLAGS) -o $@ host/test_image.c src/image.c src/protocol.c

host/pack_pbm: host/pack_pbm.c src/image.c src/protocol.c
	$(CC) $(CFLAGS) -o $@ host/pack_pbm.c src/image.c src/protocol.c

test: $(HOST_BIN)
	./host/test_protocol
	./host/test_image

MCU_CC = arm-none-eabi-gcc
MCU_CFLAGS = -std=c11 -Wall -Wextra -Werror -Iinclude -mcpu=cortex-m0plus -mthumb \
	-ffunction-sections -fdata-sections -Os
MCU_LDFLAGS = -T stm32g071.ld -nostartfiles -Wl,--gc-sections
MCU_SRC = src/main.c src/protocol.c src/image.c src/ntag.c src/epd.c src/hal.c src/startup.c

mcu:
	@if ! command -v $(MCU_CC) >/dev/null 2>&1; then \
		echo "arm-none-eabi-gcc not installed; host tests still run."; \
		exit 0; \
	fi
	$(MCU_CC) $(MCU_CFLAGS) $(MCU_SRC) $(MCU_LDFLAGS) -o nfc-eink.elf
	arm-none-eabi-objcopy -O binary nfc-eink.elf nfc-eink.bin
	arm-none-eabi-size nfc-eink.elf

clean:
	rm -f $(HOST_BIN) nfc-eink.elf nfc-eink.bin
