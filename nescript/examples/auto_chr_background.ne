// Auto-CHR background — first NEScript example to use the
// `@nametable("file.png")` shortcut without supplying any matching
// CHR data. Previously the resolver decoded the PNG into a tile
// index table but left CHR generation to the user; the new
// `png_to_nametable_with_chr` helper also generates the per-tile
// CHR bytes from the same brightness-bucketing code that
// `png_to_chr` uses for sprite imports, then the asset resolver
// allocates contiguous CHR-ROM tile indices starting after the
// last sprite tile and rewrites the nametable to point at them.
//
// `auto_chr_bg.png` is a 256×240 grayscale gradient rendered to
// roughly fifty distinct tiles — enough variety to exercise the
// dedupe + CHR generation path but well within the 256-tile cap.
//
// Build: cargo run -- build examples/auto_chr_background.ne

game "Auto CHR Background" {
    mapper: NROM
}

// Grayscale palette with every background sub-palette set to the
// same three shades. The PNG-to-attribute helper buckets each
// 16×16 quadrant by average brightness and assigns sub-palette
// 0..3, so we need *every* bg sub-palette to carry the same
// dk_gray / lt_gray / white triple — otherwise quadrants that
// pick a non-zero palette would render as the universal colour.
palette Main {
    universal: black
    bg0: [dk_gray, lt_gray, white]
    bg1: [dk_gray, lt_gray, white]
    bg2: [dk_gray, lt_gray, white]
    bg3: [dk_gray, lt_gray, white]
    sp0: [black, black, black]
    sp1: [black, black, black]
    sp2: [black, black, black]
    sp3: [black, black, black]
}

// `@nametable` is the shortcut form: no `tiles:` / `attributes:`
// body, and the resolver fills both — and now CHR data too — from
// the PNG itself.
background Stage @nametable("auto_chr_bg.png")

on frame {
    wait_frame
}

start Main
