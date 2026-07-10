#!/usr/bin/env python3
"""Build Mega Man widget sprite assets.

Metal Man frames are sliced from the authentic sheet at
`Shared/MegaManWidget/SourcesSheets/metal-man.gif` (walk / throw / jump / blade).

Other characters still use simple original placeholder pixel art until real
sheets are added the same way.
"""

from __future__ import annotations

import json
from io import BytesIO
from pathlib import Path

from PIL import Image

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "Shared" / "MegaManWidget" / "Assets.xcassets"
SHEETS = ROOT / "Shared" / "MegaManWidget" / "SourcesSheets"
METAL_SHEET = SHEETS / "metal-man.gif"

SIZE = 32
SCALE_PLACEHOLDER = 4
T = None

PLACEHOLDER_CHARS = {
    "mega-man": {
        "name": "Mega Man",
        "colors": {
            "O": (20, 20, 40),
            "B": (0, 112, 236),
            "D": (0, 56, 168),
            "C": (0, 232, 216),
            "S": (252, 216, 168),
            "W": (252, 252, 252),
            "R": (248, 56, 0),
            "Y": (252, 216, 0),
        },
    },
    "wood-man": {
        "name": "Wood Man",
        "colors": {
            "O": (40, 24, 8),
            "B": (152, 88, 40),
            "D": (96, 48, 16),
            "C": (72, 168, 48),
            "S": (252, 216, 168),
            "W": (232, 200, 120),
            "R": (200, 48, 32),
            "Y": (200, 220, 64),
        },
    },
    "heat-man": {
        "name": "Heat Man",
        "colors": {
            "O": (40, 8, 0),
            "B": (248, 120, 0),
            "D": (184, 48, 0),
            "C": (252, 200, 64),
            "S": (252, 216, 168),
            "W": (252, 252, 200),
            "R": (248, 32, 0),
            "Y": (252, 252, 0),
        },
    },
    "flash-man": {
        "name": "Flash Man",
        "colors": {
            "O": (8, 24, 64),
            "B": (48, 120, 248),
            "D": (24, 56, 168),
            "C": (120, 216, 252),
            "S": (252, 216, 168),
            "W": (252, 252, 252),
            "R": (248, 200, 0),
            "Y": (252, 252, 120),
        },
    },
    "quick-man": {
        "name": "Quick Man",
        "colors": {
            "O": (48, 0, 0),
            "B": (216, 40, 40),
            "D": (136, 16, 16),
            "C": (252, 120, 120),
            "S": (252, 216, 168),
            "W": (252, 252, 252),
            "R": (252, 200, 0),
            "Y": (252, 252, 0),
        },
    },
    "crash-man": {
        "name": "Crash Man",
        "colors": {
            "O": (40, 8, 8),
            "B": (232, 72, 48),
            "D": (152, 32, 24),
            "C": (252, 160, 96),
            "S": (252, 216, 168),
            "W": (252, 252, 252),
            "R": (80, 80, 96),
            "Y": (252, 216, 0),
        },
    },
    "bubble-man": {
        "name": "Bubble Man",
        "colors": {
            "O": (0, 32, 64),
            "B": (32, 144, 216),
            "D": (16, 72, 136),
            "C": (120, 216, 248),
            "S": (252, 216, 168),
            "W": (232, 248, 252),
            "R": (248, 120, 160),
            "Y": (200, 240, 252),
        },
    },
    "air-man": {
        "name": "Air Man",
        "colors": {
            "O": (24, 16, 40),
            "B": (120, 104, 168),
            "D": (64, 48, 104),
            "C": (184, 168, 216),
            "S": (252, 216, 168),
            "W": (240, 240, 248),
            "R": (200, 64, 96),
            "Y": (252, 216, 0),
        },
    },
}


def grid(*rows: str) -> list[str]:
    assert all(len(r) == SIZE for r in rows), f"expected {SIZE}-wide rows"
    assert len(rows) == SIZE
    return list(rows)


STAND = grid(
    "................................",
    "................................",
    "............OOOOOO..............",
    "...........OBBBBBOO.............",
    "..........OBWWWWBBO.............",
    "..........OBWSWSBBO.............",
    "..........OBSSSSBBO.............",
    "...........OBSSBOO..............",
    "..........OODDDDOO..............",
    ".........ODBCCCCBDO.............",
    "........ODBCCCCCCBDO............",
    "........ODBCCCCCCBDO............",
    "........OOBCCCCCCBOO............",
    ".........OBBCCCCBBO.............",
    "..........OOBBBBOO..............",
    ".........ODBBOOBBDO.............",
    "........ODBBO..OBBDO............",
    ".......ODBBO....OBBDO...........",
    ".......OBBBO....OBBBO...........",
    ".......OBBDO....ODBBO...........",
    ".......OOBBO....OBBOO...........",
    "........OBBO....OBBO............",
    "........OBDO....ODBO............",
    "........OBBO....OBBO............",
    ".......OOBBO....OBBOO...........",
    ".......OBBBO....OBBBO...........",
    ".......ODDDO....ODDDO...........",
    "........OOOO....OOOO............",
    "................................",
    "................................",
    "................................",
    "................................",
)

WALK_A = grid(
    "................................",
    "................................",
    "............OOOOOO..............",
    "...........OBBBBBOO.............",
    "..........OBWWWWBBO.............",
    "..........OBWSWSBBO.............",
    "..........OBSSSSBBO.............",
    "...........OBSSBOO..............",
    "..........OODDDDOO..............",
    ".........ODBCCCCBDO.............",
    "........ODBCCCCCCBDO............",
    "........ODBCCCCCCBDO............",
    "........OOBCCCCCCBOO............",
    ".........OBBCCCCBBO.............",
    "..........OOBBBBOO..............",
    ".........ODBBOOBBDO.............",
    "........ODBBO..OBBDO............",
    ".......ODBBO....OBBDO...........",
    "......ODBBO......OBBDO..........",
    "......OBBBO......OBBBO..........",
    "......OOBBO......OBBOO..........",
    ".......OBBO......OBBO...........",
    ".......OBDO......ODBO...........",
    "......OOBBO......OBBOO..........",
    ".....OBBBBO......OBBBBO.........",
    ".....ODDDDO......ODDDDO.........",
    "......OOOO........OOOO..........",
    "................................",
    "................................",
    "................................",
    "................................",
    "................................",
)

WALK_B = grid(
    "................................",
    "................................",
    "............OOOOOO..............",
    "...........OBBBBBOO.............",
    "..........OBWWWWBBO.............",
    "..........OBWSWSBBO.............",
    "..........OBSSSSBBO.............",
    "...........OBSSBOO..............",
    "..........OODDDDOO..............",
    ".........ODBCCCCBDO.............",
    "........ODBCCCCCCBDO............",
    "........ODBCCCCCCBDO............",
    "........OOBCCCCCCBOO............",
    ".........OBBCCCCBBO.............",
    "..........OOBBBBOO..............",
    ".........ODBBOOBBDO.............",
    "........ODBBO..OBBDO............",
    ".......ODBBO....OBBDO...........",
    ".......OBBBO....OBBBO...........",
    ".......OBBDO....ODBBO...........",
    ".......OOBBO....OBBOO...........",
    "........OBBO....OBBO............",
    ".......OOBDO....ODBOO...........",
    "......OBBBBO....OBBBBO..........",
    "......ODDDDO....ODDDDO..........",
    ".......OOOO......OOOO...........",
    "................................",
    "................................",
    "................................",
    "................................",
    "................................",
    "................................",
)

WALK_C = grid(
    "................................",
    "................................",
    "............OOOOOO..............",
    "...........OBBBBBOO.............",
    "..........OBWWWWBBO.............",
    "..........OBWSWSBBO.............",
    "..........OBSSSSBBO.............",
    "...........OBSSBOO..............",
    "..........OODDDDOO..............",
    ".........ODBCCCCBDO.............",
    "........ODBCCCCCCBDO............",
    "........ODBCCCCCCBDO............",
    "........OOBCCCCCCBOO............",
    ".........OBBCCCCBBO.............",
    "..........OOBBBBOO..............",
    ".........ODBBOOBBDO.............",
    "........ODBBO..OBBDO............",
    ".......ODBBO....OBBDO...........",
    "......ODBBO......OBBDO..........",
    ".....ODBBO........OBBDO.........",
    ".....OBBBO........OBBBO.........",
    ".....OOBBO........OBBOO.........",
    "......OBDO........ODBO..........",
    ".....OOBBO........OBBOO.........",
    "....OBBBBO........OBBBBO........",
    "....ODDDDO........ODDDDO........",
    ".....OOOO..........OOOO.........",
    "................................",
    "................................",
    "................................",
    "................................",
    "................................",
)

SHOOT = grid(
    "................................",
    "................................",
    "............OOOOOO..............",
    "...........OBBBBBOO.............",
    "..........OBWWWWBBO.............",
    "..........OBWSWSBBO.............",
    "..........OBSSSSBBO.............",
    "...........OBSSBOO..............",
    "..........OODDDDOO..............",
    ".........ODBCCCCBDO.............",
    "........ODBCCCCCCBDO............",
    "........ODBCCCCCCBDO............",
    "........OOBCCCCCCBOO............",
    ".........OBBCCCCBBO.............",
    "..........OOBBBBOO..............",
    ".........ODBBOOBBBBOOOOO........",
    "........ODBBO..OBBBBRRYYOO......",
    ".......ODBBO....OBBBOOOOO.......",
    ".......OBBBO....OBBBO...........",
    ".......OBBDO....ODBBO...........",
    ".......OOBBO....OBBOO...........",
    "........OBBO....OBBO............",
    "........OBDO....ODBO............",
    "........OBBO....OBBO............",
    ".......OOBBO....OBBOO...........",
    ".......OBBBO....OBBBO...........",
    ".......ODDDO....ODDDO...........",
    "........OOOO....OOOO............",
    "................................",
    "................................",
    "................................",
    "................................",
)

JUMP = grid(
    "................................",
    "............OOOOOO..............",
    "...........OBBBBBOO.............",
    "..........OBWWWWBBO.............",
    "..........OBWSWSBBO.............",
    "..........OBSSSSBBO.............",
    "...........OBSSBOO..............",
    "..........OODDDDOO..............",
    ".........ODBCCCCBDO.............",
    "........ODBCCCCCCBDO............",
    "........ODBCCCCCCBDO............",
    "........OOBCCCCCCBOO............",
    ".........OBBCCCCBBO.............",
    "..........OOBBBBOO..............",
    ".........ODBBOOBBDO.............",
    "........ODBBO..OBBDO............",
    ".......ODBBO....OBBDO...........",
    "......ODBBO......OBBDO..........",
    ".....ODBBO........OBBDO.........",
    ".....OBBBO........OBBBO.........",
    ".....OOBBO........OBBOO.........",
    "......OBBO........OBBO..........",
    ".....OOBDO........ODBOO.........",
    "....OBBBBO........OBBBBO........",
    "....ODDDDO........ODDDDO........",
    ".....OOOO..........OOOO.........",
    "................................",
    "................................",
    "................................",
    "................................",
    "................................",
    "................................",
)

JUMP_SHOOT = grid(
    "................................",
    "............OOOOOO..............",
    "...........OBBBBBOO.............",
    "..........OBWWWWBBO.............",
    "..........OBWSWSBBO.............",
    "..........OBSSSSBBO.............",
    "...........OBSSBOO..............",
    "..........OODDDDOO..............",
    ".........ODBCCCCBDO.............",
    "........ODBCCCCCCBDO............",
    "........ODBCCCCCCBDO............",
    "........OOBCCCCCCBOO............",
    ".........OBBCCCCBBO.............",
    "..........OOBBBBOO..............",
    ".........ODBBOOBBBBOOOOO........",
    "........ODBBO..OBBBBRRYYOO......",
    ".......ODBBO....OBBBOOOOO.......",
    "......ODBBO......OBBDO..........",
    ".....ODBBO........OBBDO.........",
    ".....OBBBO........OBBBO.........",
    ".....OOBBO........OBBOO.........",
    "......OBBO........OBBO..........",
    ".....OOBDO........ODBOO.........",
    "....OBBBBO........OBBBBO........",
    "....ODDDDO........ODDDDO........",
    ".....OOOO..........OOOO.........",
    "................................",
    "................................",
    "................................",
    "................................",
    "................................",
    "................................",
)

LAND = grid(
    "................................",
    "................................",
    "................................",
    "............OOOOOO..............",
    "...........OBBBBBOO.............",
    "..........OBWWWWBBO.............",
    "..........OBWSWSBBO.............",
    "..........OBSSSSBBO.............",
    "...........OBSSBOO..............",
    "..........OODDDDOO..............",
    ".........ODBCCCCBDO.............",
    "........ODBCCCCCCBDO............",
    "........ODBCCCCCCBDO............",
    "........OOBCCCCCCBOO............",
    ".........OBBCCCCBBO.............",
    "..........OOBBBBOO..............",
    ".........ODBBOOBBDO.............",
    "........ODBBO..OBBDO............",
    ".......ODBBO....OBBDO...........",
    "......ODBBO......OBBDO..........",
    "......OBBBO......OBBBO..........",
    "......OOBBO......OBBOO..........",
    ".......OBDO......ODBO...........",
    "......OOBBO......OBBOO..........",
    ".....OBBBBO......OBBBBO.........",
    ".....ODDDDO......ODDDDO.........",
    "......OOOO........OOOO..........",
    "................................",
    "................................",
    "................................",
    "................................",
    "................................",
)

PLACEHOLDER_FRAMES = [
    ("00", WALK_A),
    ("01", WALK_B),
    ("02", WALK_C),
    ("03", SHOOT),
    ("04", JUMP),
    ("05", JUMP_SHOOT),
    ("06", LAND),
    ("07", STAND),
]


def is_bg(c: tuple[int, int, int, int]) -> bool:
    r, g, b, a = c
    return a < 10 or (r + g + b) < 30


def write_imageset(imageset: Path, img: Image.Image, name: str) -> None:
    imageset.mkdir(parents=True, exist_ok=True)
    buf = BytesIO()
    img.save(buf, format="PNG")
    (imageset / f"{name}.png").write_bytes(buf.getvalue())
    (imageset / "Contents.json").write_text(
        json.dumps(
            {
                "images": [{"filename": f"{name}.png", "idiom": "universal", "scale": "1x"}],
                "info": {"author": "xcode", "version": 1},
            },
            indent=2,
        )
        + "\n"
    )


def render_placeholder(rows: list[str], palette: dict[str, tuple[int, int, int]]) -> Image.Image:
    img = Image.new("RGBA", (SIZE, SIZE), (255, 255, 255, 255))
    px = img.load()
    for y, row in enumerate(rows):
        for x, ch in enumerate(row):
            if ch == ".":
                px[x, y] = (255, 255, 255, 255)
            else:
                px[x, y] = (*palette[ch], 255)
    return img.resize((SIZE * SCALE_PLACEHOLDER, SIZE * SCALE_PLACEHOLDER), Image.NEAREST)


def slice_metal_man_sheet(path: Path) -> list[Image.Image]:
    src = Image.open(path).convert("RGBA")
    w, h = src.size
    px = src.load()
    cols_has = [any(not is_bg(px[x, y]) for y in range(h)) for x in range(w)]
    spans: list[tuple[int, int]] = []
    start = None
    for x, has in enumerate(cols_has):
        if has and start is None:
            start = x
        elif not has and start is not None:
            spans.append((start, x - 1))
            start = None
    if start is not None:
        spans.append((start, w - 1))
    if len(spans) != 11:
        raise SystemExit(f"expected 11 Metal Man sprites, found {len(spans)} in {path}")

    frames: list[Image.Image] = []
    for x0, x1 in spans:
        crop = src.crop((x0, 0, x1 + 1, h))
        cpx = crop.load()
        cw, ch = crop.size
        ys = [y for y in range(ch) if any(not is_bg(cpx[x, y]) for x in range(cw))]
        xs = [x for x in range(cw) if any(not is_bg(cpx[x, y]) for y in range(ch))]
        tight = crop.crop((xs[0], ys[0], xs[-1] + 1, ys[-1] + 1)).convert("RGBA")
        tp = tight.load()
        for yy in range(tight.size[1]):
            for xx in range(tight.size[0]):
                if is_bg(tp[xx, yy]):
                    tp[xx, yy] = (255, 255, 255, 255)
        frames.append(tight)
    return frames


def to_square(im: Image.Image, size: int, flip: bool = False) -> Image.Image:
    src_im = im.transpose(Image.FLIP_LEFT_RIGHT) if flip else im
    canvas = Image.new("RGBA", (size, size), (255, 255, 255, 255))
    ox = (size - src_im.size[0]) // 2
    oy = size - src_im.size[1]
    canvas.paste(src_im, (ox, oy), src_im)
    return canvas


def paste_nonwhite(base: Image.Image, overlay: Image.Image, anchor: tuple[int, int]) -> Image.Image:
    out = base.copy()
    op = out.load()
    bp = overlay.load()
    ax, ay = anchor
    for y in range(overlay.size[1]):
        for x in range(overlay.size[0]):
            r, g, b, a = bp[x, y]
            if (r, g, b) != (255, 255, 255) and a > 0:
                xx, yy = ax + x, ay + y
                if 0 <= xx < out.size[0] and 0 <= yy < out.size[1]:
                    op[xx, yy] = (r, g, b, 255)
    return out


def build_metal_man_loop(sheet: Path, scale: int = 6) -> list[Image.Image]:
    """Sheet order: idle, ready, throw_a, throw_b, walk×3, jump, hurt, blade×2."""
    raw = slice_metal_man_sheet(sheet)
    # Persist labeled slices next to the sheet for inspection / reuse.
    frames_dir = SHEETS / "metal-man-frames"
    frames_dir.mkdir(parents=True, exist_ok=True)
    labels = [
        "idle",
        "ready",
        "throw_a",
        "throw_b",
        "walk_a",
        "walk_b",
        "walk_c",
        "jump",
        "hurt",
        "blade_a",
        "blade_b",
    ]
    for i, (lab, fr) in enumerate(zip(labels, raw)):
        fr.save(frames_dir / f"{i:02d}_{lab}.png")

    max_dim = max(max(f.size) for f in raw[:9])
    chars = [to_square(f, max_dim, flip=True) for f in raw[:9]]
    blade_a = to_square(raw[9], max_dim, flip=False)
    blade_b = to_square(raw[10], max_dim, flip=False)

    throw_release = paste_nonwhite(
        chars[3],
        blade_a,
        (int(max_dim * 0.55), int(max_dim * 0.05)),
    )
    jump_throw = paste_nonwhite(
        chars[7],
        blade_b,
        (int(max_dim * 0.58), int(max_dim * 0.0)),
    )

    loop = [
        chars[4],  # walk_a
        chars[5],  # walk_b
        chars[6],  # walk_c
        chars[2],  # throw wind-up
        throw_release,
        chars[7],  # jump
        jump_throw,
        chars[0],  # idle
    ]
    return [f.resize((max_dim * scale, max_dim * scale), Image.NEAREST) for f in loop]


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "Contents.json").write_text(
        json.dumps({"info": {"author": "xcode", "version": 1}}, indent=2) + "\n"
    )

    catalog = []

    # Metal Man from authentic sheet
    if not METAL_SHEET.exists():
        raise SystemExit(f"missing Metal Man sheet: {METAL_SHEET}")
    for i, img in enumerate(build_metal_man_loop(METAL_SHEET)):
        name = f"metal-man_{i:02d}"
        write_imageset(OUT / f"{name}.imageset", img, name)
    catalog.append({"id": "metal-man", "name": "Metal Man", "frameCount": 8, "source": "sheet"})

    for char_id, meta in PLACEHOLDER_CHARS.items():
        palette = meta["colors"]
        for frame_id, rows in PLACEHOLDER_FRAMES:
            asset_name = f"{char_id}_{frame_id}"
            img = render_placeholder(rows, palette)
            write_imageset(OUT / f"{asset_name}.imageset", img, asset_name)
        catalog.append(
            {"id": char_id, "name": meta["name"], "frameCount": len(PLACEHOLDER_FRAMES), "source": "placeholder"}
        )

    manifest = OUT.parent / "sprite-manifest.json"
    manifest.write_text(json.dumps({"characters": catalog, "frameCount": 8}, indent=2) + "\n")
    print(f"Wrote assets for {len(catalog)} characters to {OUT}")


if __name__ == "__main__":
    main()
