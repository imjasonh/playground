#ifndef NFC_EINK_NTAG_H
#define NFC_EINK_NTAG_H

#include <stddef.h>
#include <stdint.h>

/*
 * NT3H2111/2211 session registers (I2C block 0xFE).
 * Bit positions are from NXP NT3H2111_2211 Table 14. The previous
 * masks swapped PTHRU with TRANSFER_DIR and polled I2C_LOCKED as
 * if it were SRAM_RF_READY, so the mailbox never ran.
 */
enum {
    NTAG_NC_TRANSFER_DIR = 0x01, /* 1: NFC -> I2C */
    NTAG_NC_SRAM_MIRROR = 0x02,
    NTAG_NC_FD_ON = 0x0C,        /* 11b: FD low when SRAM is ready */
    NTAG_NC_FD_OFF = 0x30,       /* 11b: FD high after I2C finishes */
    NTAG_NC_PTHRU = 0x40,
    NTAG_NC_I2C_RST = 0x80,
    NTAG_NS_RF_FIELD = 0x01,
    NTAG_NS_EE_BUSY = 0x02,
    NTAG_NS_EE_ERR = 0x04,
    NTAG_NS_SRAM_RF_READY = 0x08,
    NTAG_NS_SRAM_I2C_READY = 0x10,
    NTAG_NS_RF_LOCKED = 0x20,
    NTAG_NS_I2C_LOCKED = 0x40,
    NTAG_NS_NDEF_READ = 0x80
};

int ntag_read_block(uint8_t block, uint8_t *data, size_t len);
int ntag_write_block(uint8_t block, const uint8_t *data, size_t len);
int ntag_read_session(uint8_t *nc, uint8_t *ns);
int ntag_enable_passthru(void);
int ntag_poll_sram(uint8_t chunk[64], uint32_t spins);

#endif
