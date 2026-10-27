// DPCM demo. A short sample loops on the DMC from the first frame,
// so the frame-180 audio hash includes it.
//
// Build:  cargo run -- build examples/dpcm_demo.ne

game "DPCM Demo" {
    mapper: NROM
}

dpcm Buzz {
    rate: 15
    loop: true
    data: [0x55, 0x55, 0xAA, 0xAA, 0x55, 0x55, 0xAA, 0xAA, 0x0F, 0xF0, 0x0F, 0xF0, 0x33, 0xCC, 0x33, 0xCC]
}

var played: u8 = 0

on frame {
    if played == 0 {
        play_dpcm Buzz
        played = 1
    }
}

start Main
