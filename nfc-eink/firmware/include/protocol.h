#ifndef NFC_EINK_PROTOCOL_H
#define NFC_EINK_PROTOCOL_H

#include <stddef.h>
#include <stdint.h>

enum {
    FRAME_W = 400,
    FRAME_H = 300,
    FRAME_BYTES = 15000,
    CHUNK_SIZE = 64,
    HEADER_SIZE = 8,
    PAYLOAD_BYTES = HEADER_SIZE + FRAME_BYTES,
    CHUNK_COUNT = (PAYLOAD_BYTES + CHUNK_SIZE - 1) / CHUNK_SIZE
};

#define EINK_MAGIC0 'E'
#define EINK_MAGIC1 'I'
#define EINK_MAGIC2 'N'
#define EINK_MAGIC3 'K'

uint16_t eink_crc16(const uint8_t *data, size_t len);
void eink_write_header(uint8_t out[HEADER_SIZE], uint16_t nbytes, uint16_t crc);
int eink_parse_header(const uint8_t in[HEADER_SIZE], uint16_t *nbytes, uint16_t *crc);
size_t eink_chunk_count(size_t payload_len);
void eink_fill_chunk(uint8_t chunk[CHUNK_SIZE], size_t index, const uint8_t *payload, size_t payload_len);
int eink_absorb_chunk(uint8_t *payload, size_t payload_cap, size_t index, const uint8_t chunk[CHUNK_SIZE], size_t *filled);

#endif
