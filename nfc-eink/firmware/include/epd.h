#ifndef NFC_EINK_EPD_H
#define NFC_EINK_EPD_H

#include <stdint.h>

#include "protocol.h"

void epd_hw_reset(void);
void epd_init(void);
void epd_write_frame(const uint8_t frame[FRAME_BYTES]);
void epd_refresh(void);
void epd_sleep(void);

#endif
