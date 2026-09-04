#include "image.h"

#include <string.h>

static int is_ws(int c)
{
    return c == ' ' || c == '\n' || c == '\r' || c == '\t';
}

static int skip_ws_and_comments(const uint8_t *p, size_t n, size_t *i)
{
    while (*i < n) {
        if (p[*i] == '#') {
            while (*i < n && p[*i] != '\n') {
                (*i)++;
            }
            continue;
        }
        if (!is_ws(p[*i])) {
            return 0;
        }
        (*i)++;
    }
    return -1;
}

static int read_uint(const uint8_t *p, size_t n, size_t *i, int *out)
{
    int v = 0;
    int got = 0;

    if (skip_ws_and_comments(p, n, i) != 0) {
        return -1;
    }
    while (*i < n && p[*i] >= '0' && p[*i] <= '9') {
        v = v * 10 + (p[*i] - '0');
        (*i)++;
        got = 1;
    }
    if (!got) {
        return -1;
    }
    *out = v;
    return 0;
}

void eink_fill_test_pattern(uint8_t frame[FRAME_BYTES])
{
    int y;
    int xbyte;

    memset(frame, 0xFF, FRAME_BYTES);
    for (y = 0; y < FRAME_H; y++) {
        for (xbyte = 0; xbyte < FRAME_W / 8; xbyte++) {
            if (((y / 16) + xbyte) % 2 == 0) {
                frame[y * (FRAME_W / 8) + xbyte] = 0x00;
            }
        }
        if (y < 8 || y >= FRAME_H - 8) {
            memset(frame + y * (FRAME_W / 8), 0x00, FRAME_W / 8);
        }
    }
}

int eink_pack_pbm(const uint8_t *pbm, size_t pbm_len, uint8_t frame[FRAME_BYTES])
{
    size_t i = 0;
    int kind;
    int w = 0;
    int h = 0;
    int x;
    int y;

    if (pbm_len < 3 || pbm[0] != 'P' || (pbm[1] != '1' && pbm[1] != '4')) {
        return -1;
    }
    kind = pbm[1];
    i = 2;
    if (read_uint(pbm, pbm_len, &i, &w) != 0 || read_uint(pbm, pbm_len, &i, &h) != 0) {
        return -2;
    }
    if (w != FRAME_W || h != FRAME_H) {
        return -3;
    }
    memset(frame, 0xFF, FRAME_BYTES);
    if (kind == '4') {
        if (skip_ws_and_comments(pbm, pbm_len, &i) != 0) {
            return -2;
        }
        if (i < pbm_len && is_ws(pbm[i])) {
            i++;
        }
        if (pbm_len - i < FRAME_BYTES) {
            return -4;
        }
        memcpy(frame, pbm + i, FRAME_BYTES);
        return 0;
    }
    for (y = 0; y < FRAME_H; y++) {
        for (x = 0; x < FRAME_W; x++) {
            int bit;

            if (skip_ws_and_comments(pbm, pbm_len, &i) != 0) {
                return -4;
            }
            if (pbm[i] != '0' && pbm[i] != '1') {
                return -5;
            }
            bit = pbm[i] - '0';
            i++;
            /* PBM 1 is black. SSD1683 0 is black. */
            if (bit) {
                frame[y * (FRAME_W / 8) + x / 8] &= (uint8_t)~(0x80 >> (x % 8));
            }
        }
    }
    return 0;
}
