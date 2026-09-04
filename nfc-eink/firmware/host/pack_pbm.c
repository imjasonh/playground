#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "image.h"
#include "protocol.h"

int main(int argc, char **argv)
{
    FILE *in;
    FILE *out;
    uint8_t *pbm;
    uint8_t frame[FRAME_BYTES];
    uint8_t payload[PAYLOAD_BYTES];
    uint8_t chunk[CHUNK_SIZE];
    long sz;
    size_t i;
    uint16_t crc;
    const char *out_path;

    if (argc < 2) {
        fprintf(stderr, "usage: pack_pbm in.pbm [out.eink]\n");
        return 2;
    }
    out_path = (argc > 2) ? argv[2] : "frame.eink";
    in = fopen(argv[1], "rb");
    if (in == NULL) {
        perror(argv[1]);
        return 1;
    }
    if (fseek(in, 0, SEEK_END) != 0) {
        fclose(in);
        return 1;
    }
    sz = ftell(in);
    if (sz < 0 || sz > 400000) {
        fclose(in);
        return 1;
    }
    rewind(in);
    pbm = (uint8_t *)malloc((size_t)sz);
    if (pbm == NULL) {
        fclose(in);
        return 1;
    }
    if (fread(pbm, 1, (size_t)sz, in) != (size_t)sz) {
        free(pbm);
        fclose(in);
        return 1;
    }
    fclose(in);
    if (eink_pack_pbm(pbm, (size_t)sz, frame) != 0) {
        fprintf(stderr, "not a 400x300 PBM\n");
        free(pbm);
        return 1;
    }
    free(pbm);
    crc = eink_crc16(frame, FRAME_BYTES);
    eink_write_header(payload, FRAME_BYTES, crc);
    memcpy(payload + HEADER_SIZE, frame, FRAME_BYTES);
    out = fopen(out_path, "wb");
    if (out == NULL) {
        perror(out_path);
        return 1;
    }
    for (i = 0; i < CHUNK_COUNT; i++) {
        eink_fill_chunk(chunk, i, payload, PAYLOAD_BYTES);
        if (fwrite(chunk, 1, CHUNK_SIZE, out) != CHUNK_SIZE) {
            fclose(out);
            return 1;
        }
    }
    fclose(out);
    printf("wrote %s (%u chunks, crc=0x%04x)\n", out_path, (unsigned)CHUNK_COUNT, crc);
    return 0;
}
