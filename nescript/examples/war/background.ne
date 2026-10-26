// war/background.ne — the static 32×30 nametable loaded at reset.
//
// NEScript loads the *first* declared `background` into nametable 0
// before rendering is enabled, so whatever this file declares is
// visible on frame 0 of the ROM. We use a single felt-table
// background — every cell is the dedicated TILE_FELT_BG (tile 75
// in the Tileset sprite, a sparse cross-hatch authored to look
// like dk_green felt with mint flecks when rendered through bg
// sub-palette 0). All UI (title banner, "PRESS A", win banners,
// face-up cards, etc.) is drawn on top via sprites so we never
// pay the cost of a full mid-frame nametable swap.
//
// The `palette_map:` field is omitted on purpose: every attribute
// byte defaults to 0, which selects bg sub-palette 0 for every
// metatile. That's the felt palette declared in the top-level
// war.ne (forest / green / mint over a dk_green universal).

background Felt {
    legend {
        ".": 75      // TILE_FELT_BG — sparse mint flecks on dk_green
    }
    map: [
        "................................",
        "................................",
        "................................",
        "................................",
        "................................",
        "................................",
        "................................",
        "................................",
        "................................",
        "................................",
        "................................",
        "................................",
        "................................",
        "................................",
        "................................",
        "................................",
        "................................",
        "................................",
        "................................",
        "................................",
        "................................",
        "................................",
        "................................",
        "................................",
        "................................",
        "................................",
        "................................",
        "................................",
        "................................",
        "................................"
    ]
}
