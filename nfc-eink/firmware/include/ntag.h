#ifndef NFC_EINK_NTAG_H
#define NFC_EINK_NTAG_H

#include <stddef.h>
#include <stdint.h>

enum {
    NTAG_NS_RF_FIELD = 0x80,
    NTAG_NS_SRAM_RF_READY = 0x40,
    NTAG_NS_SRAM_I2C_READY = 0x20,
    NTAG_NC_PTHRU = 0x01,
    NTAG_NC_DIR_RF_TO_I2C = 0x80
};

int ntag_read_block(uint8_t block, uint8_t *data, size_t len);
int ntag_write_block(uint8_t block, const uint8_t *data, size_t len);
int ntag_read_session(uint8_t *nc, uint8_t *ns);
int ntag_enable_passthru(void);
int ntag_poll_sram(uint8_t chunk[64]);

#endif
