#include "ntag.h"

#include "board.h"
#include "hal.h"

int ntag_read_block(uint8_t block, uint8_t *data, size_t len)
{
    if (i2c_write(NTAG_I2C_ADDR, &block, 1) != 0) {
        i2c_recover();
        if (i2c_write(NTAG_I2C_ADDR, &block, 1) != 0) {
            return -1;
        }
    }
    if (i2c_read(NTAG_I2C_ADDR, data, (uint32_t)len) != 0) {
        i2c_recover();
        return -1;
    }
    return 0;
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
    if (i2c_write(NTAG_I2C_ADDR, buf, (uint32_t)(len + 1)) != 0) {
        i2c_recover();
        return i2c_write(NTAG_I2C_ADDR, buf, (uint32_t)(len + 1));
    }
    return 0;
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
    uint8_t nc = 0;
    uint8_t ns = 0;
    uint32_t wait = 4000;

    /* Pass-through only sticks when both VCC and the RF field are up. */
    while (wait--) {
        iwdg_kick();
        if (ntag_read_session(&nc, &ns) != 0) {
            continue;
        }
        if (ns & NTAG_NS_RF_FIELD) {
            break;
        }
    }
    if ((ns & NTAG_NS_RF_FIELD) == 0) {
        return -2;
    }
    if (ntag_read_block(NTAG_SESS_BLK, sess, 8) != 0) {
        return -1;
    }
    sess[0] = (uint8_t)((sess[0] & NTAG_NC_I2C_RST) | NTAG_NC_PTHRU |
                        NTAG_NC_FD_ON | NTAG_NC_FD_OFF | NTAG_NC_TRANSFER_DIR);
    return ntag_write_block(NTAG_SESS_BLK, sess, 8);
}

int ntag_poll_sram(uint8_t chunk[64], uint32_t spins)
{
    uint8_t nc;
    uint8_t ns;

    while (spins--) {
        iwdg_kick();
        if (ntag_read_session(&nc, &ns) != 0) {
            continue;
        }
        if (ns & NTAG_NS_SRAM_I2C_READY) {
            return ntag_read_block(NTAG_SRAM_BLK, chunk, 64);
        }
        /* FD_ON=11b: FD low means the SRAM page is waiting for I2C. */
        if ((gpio_in(GPIO_PORTB, PIN_NFC_FD) == 0) && (ns & NTAG_NS_RF_FIELD)) {
            if (ntag_read_block(NTAG_SRAM_BLK, chunk, 64) == 0) {
                return 0;
            }
        }
    }
    return -2;
}
