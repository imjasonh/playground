#!/usr/bin/env python3
"""Generate original NES-style Mega Man 2–inspired sprite frames for the widget.

These are original pixel-art approximations (not Capcom rips). Each character
gets an 8-frame action loop: walk ×3, walk-shoot, jump, jump-shoot, land, idle.
Frames are written as opaque PNGs (white background) for the timer-mask stack.
"""

from __future__ import annotations

import json
from pathlib import Path

from PIL import Image

SIZE = 32
SCALE = 4  # export 128×128 for crisp widget rendering
OUT = Path(__file__).resolve().parents[1] / "Shared" / "MegaManWidget" / "Assets.xcassets"

# Transparent marker in source grids; replaced with opaque white on export.
T = None

CHARACTERS = {
    "mega-man": {
        "name": "Mega Man",
        "colors": {
            "O": (20, 20, 40),  # outline
            "B": (0, 112, 236),  # blue
            "D": (0, 56, 168),  # dark blue
            "C": (0, 232, 216),  # cyan highlight
            "S": (252, 216, 168),  # skin
            "W": (252, 252, 252),  # white
            "R": (248, 56, 0),  # red (buster flash)
            "Y": (252, 216, 0),  # yellow
        },
    },
    "metal-man": {
        "name": "Metal Man",
        "colors": {
            "O": (20, 20, 40),
            "B": (160, 160, 176),
            "D": (88, 88, 104),
            "C": (220, 220, 232),
            "S": (252, 216, 168),
            "W": (252, 252, 252),
            "R": (200, 32, 48),
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


# Base standing pose (facing right). Letters map into each character palette.
# '.' = transparent (becomes white on export), space unused.
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

# 8-frame action loop used by the widget.
FRAMES = [
    ("00", WALK_A),
    ("01", WALK_B),
    ("02", WALK_C),
    ("03", SHOOT),
    ("04", JUMP),
    ("05", JUMP_SHOOT),
    ("06", LAND),
    ("07", STAND),
]


def render(rows: list[str], palette: dict[str, tuple[int, int, int]]) -> Image.Image:
    img = Image.new("RGBA", (SIZE, SIZE), (255, 255, 255, 255))
    px = img.load()
    for y, row in enumerate(rows):
        for x, ch in enumerate(row):
            if ch == ".":
                px[x, y] = (255, 255, 255, 255)
            else:
                rgb = palette[ch]
                px[x, y] = (*rgb, 255)
    return img.resize((SIZE * SCALE, SIZE * SCALE), Image.NEAREST)


def write_imageset(imageset: Path, png_bytes: bytes, name: str) -> None:
    imageset.mkdir(parents=True, exist_ok=True)
    (imageset / f"{name}.png").write_bytes(png_bytes)
    contents = {
        "images": [
            {
                "filename": f"{name}.png",
                "idiom": "universal",
                "scale": "1x",
            }
        ],
        "info": {"author": "xcode", "version": 1},
    }
    (imageset / "Contents.json").write_text(json.dumps(contents, indent=2) + "\n")


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "Contents.json").write_text(
        json.dumps({"info": {"author": "xcode", "version": 1}}, indent=2) + "\n"
    )

    catalog = []
    for char_id, meta in CHARACTERS.items():
        palette = meta["colors"]
        for frame_id, rows in FRAMES:
            asset_name = f"{char_id}_{frame_id}"
            img = render(rows, palette)
            from io import BytesIO

            buf = BytesIO()
            img.save(buf, format="PNG")
            write_imageset(OUT / f"{asset_name}.imageset", buf.getvalue(), asset_name)
        catalog.append({"id": char_id, "name": meta["name"], "frameCount": len(FRAMES)})

    manifest = OUT.parent / "sprite-manifest.json"
    manifest.write_text(json.dumps({"characters": catalog, "frameCount": len(FRAMES)}, indent=2) + "\n")
    print(f"Wrote {len(CHARACTERS) * len(FRAMES)} frames to {OUT}")


if __name__ == "__main__":
    main()
