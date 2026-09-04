#include <stdio.h>
#include <string.h>

#include "image.h"

static int fail(const char *msg)
{
    fprintf(stderr, "FAIL %s\n", msg);
    return 1;
}

int main(void)
{
    uint8_t frame[FRAME_BYTES];
    uint8_t p4[32 + FRAME_BYTES];
    const char *hdr = "P4\n400 300\n";
    size_t hdr_len = strlen(hdr);
    int i;

    eink_fill_test_pattern(frame);
    if (frame[0] != 0x00) {
        return fail("top bar");
    }
    memcpy(p4, hdr, hdr_len);
    memset(p4 + hdr_len, 0x00, FRAME_BYTES);
    if (eink_pack_pbm(p4, hdr_len + FRAME_BYTES, frame) != 0) {
        return fail("pack p4");
    }
    for (i = 0; i < FRAME_BYTES; i++) {
        if (frame[i] != 0x00) {
            return fail("p4 not black");
        }
    }
    if (eink_pack_pbm((const uint8_t *)"P1\n2 2\n1 0 0 1\n", 16, frame) != -3) {
        return fail("reject wrong size");
    }
    printf("ok image %u bytes\n", (unsigned)FRAME_BYTES);
    return 0;
}
