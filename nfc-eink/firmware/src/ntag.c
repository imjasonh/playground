#include "ntag.h"

#include "board.h"
#include "hal.h"

int ntag_read_block(uint8_t block, uint8_t *data, size_t len)
{
    if (i2c_write(NTAG_I2C_ADDR, &block, 1) != 0) {
        return -1;
    }
    return i2c_read(NTAG_I2C_ADDR, data, (uint32_t)len);
}

int ntag_write_block(uint8_t block, const uint8_t *data, size_t len)
{
    uint8_t buf[65];
    size_t i;

    if (len > 64) {
        return -1;
    }
    buf[0] = block;
    for (i = 0; i < len; i++) {
        buf[i + 1] = data[i];
    }
    return i2c_write(NTAG_I2C_ADDR, buf, (uint32_t)(len + 1));
}

int ntag_read_session(uint8_t *nc, uint8_t *ns)
{
    uint8_t sess[8];

    if (ntag_read_block(NTAG_SESS_BLK, sess, 8) != 0) {
        return -1;
    }
    *nc = sess[0];
    *ns = sess[6];
    return 0;
}

int ntag_enable_passthru(void)
{
    uint8_t sess[8];
    uint8_t nc;

    if (ntag_read_block(NTAG_SESS_BLK, sess, 8) != 0) {
        return -1;
    }
    nc = (uint8_t)(sess[0] | NTAG_NC_PTHRU | NTAG_NC_DIR_RF_TO_I2C);
    sess[0] = nc;
    return ntag_write_block(NTAG_SESS_BLK, sess, 8);
}

int ntag_poll_sram(uint8_t chunk[64])
{
    uint8_t nc;
    uint8_t ns;
    uint32_t spins = 200000;

    while (spins--) {
        if (ntag_read_session(&nc, &ns) != 0) {
            return -1;
        }
        if (ns & NTAG_NS_SRAM_RF_READY) {
            return ntag_read_block(NTAG_SRAM_BLK, chunk, 64);
        }
        if ((gpio_in(GPIO_PORTB, PIN_NFC_FD) == 0) && (ns & NTAG_NS_RF_FIELD)) {
            /* FD went low; try the SRAM anyway. */
            if (ntag_read_block(NTAG_SRAM_BLK, chunk, 64) == 0) {
                return 0;
            }
        }
    }
    return -2;
}
