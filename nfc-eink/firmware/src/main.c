#include "board.h"
#include "epd.h"
#include "hal.h"
#include "image.h"
#include "ntag.h"
#include "protocol.h"

static uint8_t g_payload[CHUNK_COUNT * CHUNK_SIZE];
static uint8_t g_frame[FRAME_BYTES];

static void memcpy_frame(const uint8_t *src, uint16_t nbytes)
{
    uint16_t i;
    for (i = 0; i < FRAME_BYTES; i++) {
        g_frame[i] = (i < nbytes) ? src[i] : 0xFF;
    }
}

static int receive_image(void)
{
    uint8_t chunk[CHUNK_SIZE];
    size_t filled = 0;
    size_t i;
    uint16_t nbytes = 0;
    uint16_t crc = 0;
    uint16_t got;

    if (ntag_enable_passthru() != 0) {
        uart_write("ntag passthru fail\r\n");
        return -1;
    }
    for (i = 0; i < CHUNK_COUNT; i++) {
        if (ntag_poll_sram(chunk) != 0) {
            uart_write("chunk timeout\r\n");
            return -2;
        }
        if (eink_absorb_chunk(g_payload, sizeof(g_payload), i, chunk, &filled) != 0) {
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
    memcpy_frame(g_payload + HEADER_SIZE, nbytes);
    got = eink_crc16(g_frame, nbytes);
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
        eink_fill_test_pattern(g_frame);
        uart_write("using test pattern\r\n");
    }
    if (adc_vstore_div() < VSTORE_READY_COUNTS) {
        uart_write("tank low, wait\r\n");
        hal_delay_ms(200);
    }
    epd_rail(1);
    hal_delay_ms(20);
    epd_init();
    epd_write_frame(g_frame);
    epd_refresh();
    epd_sleep();
    epd_rail(0);
    uart_write("done\r\n");
    for (;;) {
        mcu_wfi();
    }
}
