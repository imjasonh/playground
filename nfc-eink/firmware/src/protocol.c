#include "protocol.h"

#include <string.h>

uint16_t eink_crc16(const uint8_t *data, size_t len)
{
    uint16_t crc = 0xFFFF;
    size_t i;
    int bit;

    for (i = 0; i < len; i++) {
        crc ^= (uint16_t)data[i] << 8;
        for (bit = 0; bit < 8; bit++) {
            if (crc & 0x8000) {
                crc = (uint16_t)((crc << 1) ^ 0x1021);
            } else {
                crc = (uint16_t)(crc << 1);
            }
        }
    }
    return crc;
}

void eink_write_header(uint8_t out[HEADER_SIZE], uint16_t nbytes, uint16_t crc)
{
    out[0] = (uint8_t)EINK_MAGIC0;
    out[1] = (uint8_t)EINK_MAGIC1;
    out[2] = (uint8_t)EINK_MAGIC2;
    out[3] = (uint8_t)EINK_MAGIC3;
    out[4] = (uint8_t)(nbytes & 0xFF);
    out[5] = (uint8_t)(nbytes >> 8);
    out[6] = (uint8_t)(crc & 0xFF);
    out[7] = (uint8_t)(crc >> 8);
}

int eink_parse_header(const uint8_t in[HEADER_SIZE], uint16_t *nbytes, uint16_t *crc)
{
    if (in[0] != (uint8_t)EINK_MAGIC0 || in[1] != (uint8_t)EINK_MAGIC1 ||
        in[2] != (uint8_t)EINK_MAGIC2 || in[3] != (uint8_t)EINK_MAGIC3) {
        return -1;
    }
    *nbytes = (uint16_t)in[4] | ((uint16_t)in[5] << 8);
    *crc = (uint16_t)in[6] | ((uint16_t)in[7] << 8);
    if (*nbytes == 0 || *nbytes > FRAME_BYTES) {
        return -2;
    }
    return 0;
}

size_t eink_chunk_count(size_t payload_len)
{
    return (payload_len + CHUNK_SIZE - 1) / CHUNK_SIZE;
}

void eink_fill_chunk(uint8_t chunk[CHUNK_SIZE], size_t index, const uint8_t *payload, size_t payload_len)
{
    size_t off = index * CHUNK_SIZE;
    size_t n = 0;

    memset(chunk, 0, CHUNK_SIZE);
    if (off >= payload_len) {
        return;
    }
    n = payload_len - off;
    if (n > CHUNK_SIZE) {
        n = CHUNK_SIZE;
    }
    memcpy(chunk, payload + off, n);
}

int eink_absorb_chunk(uint8_t *payload, size_t payload_cap, size_t index, const uint8_t chunk[CHUNK_SIZE], size_t *filled)
{
    size_t off = index * CHUNK_SIZE;

    if (off >= payload_cap) {
        return -1;
    }
    memcpy(payload + off, chunk, CHUNK_SIZE);
    if (off + CHUNK_SIZE > *filled) {
        *filled = off + CHUNK_SIZE;
        if (*filled > payload_cap) {
            *filled = payload_cap;
        }
    }
    return 0;
}
