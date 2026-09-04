#include <stdio.h>
#include <string.h>

#include "protocol.h"

static int fail(const char *msg)
{
    fprintf(stderr, "FAIL %s\n", msg);
    return 1;
}

int main(void)
{
    uint8_t frame[FRAME_BYTES];
    uint8_t payload[PAYLOAD_BYTES];
    uint8_t chunk[CHUNK_SIZE];
    uint8_t back[PAYLOAD_BYTES];
    uint8_t hdr[HEADER_SIZE];
    uint16_t nbytes;
    uint16_t crc;
    uint16_t got;
    size_t i;
    size_t filled = 0;

    memset(frame, 0xA5, sizeof(frame));
    frame[0] = 0x00;
    frame[FRAME_BYTES - 1] = 0x11;
    crc = eink_crc16(frame, FRAME_BYTES);
    eink_write_header(hdr, FRAME_BYTES, crc);
    if (eink_parse_header(hdr, &nbytes, &got) != 0 || nbytes != FRAME_BYTES || got != crc) {
        return fail("header");
    }
    memcpy(payload, hdr, HEADER_SIZE);
    memcpy(payload + HEADER_SIZE, frame, FRAME_BYTES);
    if (eink_chunk_count(PAYLOAD_BYTES) != CHUNK_COUNT) {
        return fail("chunk count");
    }
    memset(back, 0, sizeof(back));
    for (i = 0; i < CHUNK_COUNT; i++) {
        eink_fill_chunk(chunk, i, payload, PAYLOAD_BYTES);
        if (eink_absorb_chunk(back, sizeof(back), i, chunk, &filled) != 0) {
            return fail("absorb");
        }
    }
    if (memcmp(back, payload, PAYLOAD_BYTES) != 0) {
        return fail("roundtrip");
    }
    hdr[0] = 'X';
    if (eink_parse_header(hdr, &nbytes, &got) == 0) {
        return fail("bad magic accepted");
    }
    printf("ok protocol chunks=%u crc=0x%04x\n", (unsigned)CHUNK_COUNT, crc);
    return 0;
}
