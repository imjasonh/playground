#ifndef NFC_EINK_IMAGE_H
#define NFC_EINK_IMAGE_H

#include <stddef.h>
#include <stdint.h>

#include "protocol.h"

/* Pack a 400x300 PBM (ASCII P1 or binary P4) into SSD1683 row-major
   1-bit, MSB first, 50 bytes/row. 0 is black. */
int eink_pack_pbm(const uint8_t *pbm, size_t pbm_len, uint8_t frame[FRAME_BYTES]);
void eink_fill_test_pattern(uint8_t frame[FRAME_BYTES]);

#endif
