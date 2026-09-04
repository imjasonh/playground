#include "board.h"
#include "epd.h"
#include "hal.h"
#include "ntag.h"
#include "protocol.h"

static uint8_t g_buf[CHUNK_COUNT * CHUNK_SIZE];

static int wait_vstore(void)
{
    uint32_t ms = 0;

    while (ms < VSTORE_WAIT_MS) {
        iwdg_kick();
        if (adc_vstore_div() >= VSTORE_READY_COUNTS) {
            return 0;
        }
        hal_delay_ms(20);
        ms += 20;
    }
    return -1;
}

static int receive_image(void)
{
    uint8_t chunk[CHUNK_SIZE];
    size_t filled = 0;
    size_t i;
    uint16_t nbytes = 0;
    uint16_t crc = 0;
    uint16_t got;
    uint32_t spins;

    if (ntag_enable_passthru() != 0) {
        uart_write("ntag passthru fail\r\n");
        return -1;
    }
    for (i = 0; i < CHUNK_COUNT; i++) {
        spins = (i == 0) ? NTAG_FIRST_CHUNK_SPINS : NTAG_NEXT_CHUNK_SPINS;
        if (ntag_poll_sram(chunk, spins) != 0) {
            uart_write("chunk timeout\r\n");
            return -2;
        }
        if (eink_absorb_chunk(g_buf, sizeof(g_buf), i, chunk, &filled) != 0) {
            return -3;
        }
        if (i == 0) {
            if (eink_parse_header(chunk, &nbytes, &crc) != 0) {
                uart_write("bad header\r\n");
                return -4;
            }
        }
    }
    if (nbytes > FRAME_BYTES) {
        return -5;
    }
    if (nbytes < FRAME_BYTES) {
        size_t pad;
        for (pad = nbytes; pad < FRAME_BYTES; pad++) {
            g_buf[HEADER_SIZE + pad] = 0xFF;
        }
    }
    got = eink_crc16(g_buf + HEADER_SIZE, nbytes);
    if (got != crc) {
        uart_write("crc mismatch\r\n");
        return -6;
    }
    return 0;
}

int main(void)
{
    hal_init();
    uart_write("nfc-eink\r\n");

    if (receive_image() != 0) {
        uart_write("no image, skip refresh\r\n");
        for (;;) {
            mcu_wfi();
        }
    }
    if (wait_vstore() != 0) {
        uart_write("tank low, skip refresh\r\n");
        for (;;) {
            mcu_wfi();
        }
    }
    epd_rail(1);
    hal_delay_ms(20);
    epd_init();
    epd_write_frame(g_buf + HEADER_SIZE);
    epd_refresh();
    epd_sleep();
    epd_rail(0);
    uart_write("done\r\n");
    for (;;) {
        mcu_wfi();
    }
}
