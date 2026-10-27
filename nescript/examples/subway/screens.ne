// Nametable loaders. These live in the Gfx bank with the tables they
// read. Rendering must be off.

fun load_platform_nt() {
    vram_at(0x20, 0)
    var i: u16 = 0
    while i < 1024 {
        poke(0x2007, NT_PLATFORM[i])
        i += 1
    }
    vram_at(0x24, 0)
    i = 0
    while i < 1024 {
        poke(0x2007, NT_TRAIN[i])
        i += 1
    }
}
