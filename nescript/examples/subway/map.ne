// The pause map's nametable. These live in the Map bank with NT_MAP.

// Write NT_MAP to nametable 0 and copy its attribute bytes into
// map_attr. Rendering must be off.
fun load_map_nt() {
    vram_at(0x20, 0)
    var i: u16 = 0
    while i < 960 {
        poke(0x2007, NT_MAP[i])
        i += 1
    }
    var j: u8 = 0
    while j < 64 {
        map_attr[j] = NT_MAP[960 + j as u16]
        j += 1
    }
}
