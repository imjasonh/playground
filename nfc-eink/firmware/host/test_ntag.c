#include <stdio.h>

#include "ntag.h"

static int fail(const char *msg)
{
    fprintf(stderr, "FAIL %s\n", msg);
    return 1;
}

int main(void)
{
    /* NXP NT3H2111_2211 Table 14. A wrong mask silently kills the mailbox. */
    if (NTAG_NC_TRANSFER_DIR != 0x01) {
        return fail("TRANSFER_DIR");
    }
    if (NTAG_NC_PTHRU != 0x40) {
        return fail("PTHRU");
    }
    if (NTAG_NC_FD_ON != 0x0C || NTAG_NC_FD_OFF != 0x30) {
        return fail("FD bits");
    }
    if (NTAG_NS_RF_FIELD != 0x01) {
        return fail("RF_FIELD");
    }
    if (NTAG_NS_SRAM_I2C_READY != 0x10) {
        return fail("SRAM_I2C_READY");
    }
    if (NTAG_NS_SRAM_RF_READY != 0x08) {
        return fail("SRAM_RF_READY");
    }
    if (NTAG_NS_I2C_LOCKED != 0x40) {
        return fail("I2C_LOCKED");
    }
    if ((NTAG_NC_PTHRU | NTAG_NC_TRANSFER_DIR) == 0x81) {
        return fail("old swapped NC masks");
    }
    printf("ok ntag session bits\n");
    return 0;
}
