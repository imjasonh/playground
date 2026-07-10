#!/usr/bin/env python3
"""Build Metal Man widget frames from the Mega Man 2 sheet.

Preserves black outlines (the sheet uses the same near-black for background
and outlines — naive chroma-key strips the silhouette and face details).

Animation follows the boss-fight cadence: run in place → crouch → jump →
throw Metal Blades on the way down → land → idle.
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

# Sheet palette → display colors. Body red is the classic MM2 magenta-red;
# we deepen it slightly and keep yellow / white / outline distinct.
BODY = (200, 16, 48)
YELLOW = (248, 184, 0)
WHITE = (248, 248, 248)
HIGHLIGHT = (248, 216, 120)
OUTLINE = (16, 16, 24)
BG = (255, 255, 255, 255)

SCALE = 6
# 16 frames @ 8 FPS = exactly one 2-second blink period for the timer-mask stack.
FRAME_COUNT = 16


def is_black(c: tuple[int, int, int, int]) -> bool:
    r, g, b, a = c
    return a < 10 or (r + g + b) < 30


def remap_color(c: tuple[int, int, int, int]) -> tuple[int, int, int, int]:
    r, g, b, a = c
    if is_black(c):
        return (*OUTLINE, 255)
    if (r, g, b) == (228, 0, 88):
        return (*BODY, 255)
    if (r, g, b) == (248, 184, 0):
        return (*YELLOW, 255)
    if (r, g, b) == (248, 248, 248):
        return (*WHITE, 255)
    if (r, g, b) == (248, 216, 120):
        return (*HIGHLIGHT, 255)
    return (r, g, b, 255)


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


def build_keep_mask(src: Image.Image) -> list[list[bool]]:
    """Keep colored pixels, close small gaps, then dilate for black outlines."""
    w, h = src.size
    px = src.load()
    colored = [[False] * w for _ in range(h)]
    for y in range(h):
        for x in range(w):
            if not is_black(px[x, y]):
                colored[y][x] = True

    # Close vertical gaps (torso/leg links that are only black in the sheet).
    for x in range(w):
        ys = [y for y in range(h) if colored[y][x]]
        for i in range(len(ys) - 1):
            gap = ys[i + 1] - ys[i]
            if 1 < gap <= 4:
                for y in range(ys[i] + 1, ys[i + 1]):
                    colored[y][x] = True

    # Dilate by 1 so perimeter / face / blade outlines stay with the sprite.
    keep = [[False] * w for _ in range(h)]
    for y in range(h):
        for x in range(w):
            if not colored[y][x]:
                continue
            for dy in (-1, 0, 1):
                for dx in (-1, 0, 1):
                    nx, ny = x + dx, y + dy
                    if 0 <= nx < w and 0 <= ny < h:
                        keep[ny][nx] = True
    return keep


def slice_sheet(path: Path) -> list[Image.Image]:
    src = Image.open(path).convert("RGBA")
    w, h = src.size
    px = src.load()
    keep = build_keep_mask(src)

    # Column spans from colored (non-black) pixels only — more stable than keep.
    cols = [any(not is_black(px[x, y]) for y in range(h)) for x in range(w)]
    spans: list[tuple[int, int]] = []
    start = None
    for x, has in enumerate(cols):
        if has and start is None:
            start = x
        elif not has and start is not None:
            spans.append((start, x - 1))
            start = None
    if start is not None:
        spans.append((start, w - 1))
    if len(spans) != 11:
        raise SystemExit(f"expected 11 sprites, found {len(spans)} in {path}")

    frames: list[Image.Image] = []
    for x0, x1 in spans:
        # Include outline dilation in the crop.
        xs = [x for x in range(max(0, x0 - 1), min(w, x1 + 2)) if any(keep[y][x] for y in range(h))]
        ys = [y for y in range(h) if any(keep[y][x] for x in range(xs[0], xs[-1] + 1))]
        tw, th = xs[-1] - xs[0] + 1, ys[-1] - ys[0] + 1
        canvas = Image.new("RGBA", (tw, th), BG)
        cp = canvas.load()
        for y in range(ys[0], ys[-1] + 1):
            for x in range(xs[0], xs[-1] + 1):
                if keep[y][x]:
                    cp[x - xs[0], y - ys[0]] = remap_color(px[x, y])
        frames.append(canvas)
    return frames


def to_square(im: Image.Image, size: int, flip: bool = False) -> Image.Image:
    src_im = im.transpose(Image.FLIP_LEFT_RIGHT) if flip else im
    canvas = Image.new("RGBA", (size, size), BG)
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
            if (r, g, b) != BG[:3] and a > 0:
                xx, yy = ax + x, ay + y
                if 0 <= xx < out.size[0] and 0 <= yy < out.size[1]:
                    op[xx, yy] = (r, g, b, 255)
    return out


def build_loop(sheet: Path) -> list[Image.Image]:
    """Sheet: idle, ready, throw_a, throw_b, walk×3, jump, land, blade×2."""
    raw = slice_sheet(sheet)
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
        "land",
        "blade_a",
        "blade_b",
    ]
    for i, (lab, fr) in enumerate(zip(labels, raw)):
        fr.save(frames_dir / f"{i:02d}_{lab}.png")

    max_dim = max(max(f.size) for f in raw[:9])
    idle, ready, throw_a, throw_b, walk_a, walk_b, walk_c, jump, land = [
        to_square(f, max_dim, flip=True) for f in raw[:9]
    ]
    blade_a = to_square(raw[9], max_dim, flip=False)
    blade_b = to_square(raw[10], max_dim, flip=False)

    # Throw release with spinning blade beside the raised arm (facing right).
    throw_blade_a = paste_nonwhite(throw_b, blade_a, (int(max_dim * 0.52), int(max_dim * 0.02)))
    throw_blade_b = paste_nonwhite(throw_b, blade_b, (int(max_dim * 0.52), int(max_dim * 0.02)))
    # Air throw: jump pose + blade
    air_throw_a = paste_nonwhite(jump, blade_a, (int(max_dim * 0.55), 0))
    air_throw_b = paste_nonwhite(jump, blade_b, (int(max_dim * 0.55), 0))

    # Boss-fight cadence (Metal Man runs in place, then jumps and throws on the way down).
    loop = [
        walk_a,
        walk_b,
        walk_c,
        walk_b,  # run in place
        walk_a,
        walk_b,
        ready,  # crouch / telegraph
        jump,  # leave the ground
        jump,
        air_throw_a,  # throw Metal Blade mid-air
        jump,
        air_throw_b,  # second blade (spinning)
        jump,
        land,  # hit the ground
        idle,
        ready,  # settle before the walk cycle repeats
    ]
    assert len(loop) == FRAME_COUNT
    return [f.resize((max_dim * SCALE, max_dim * SCALE), Image.NEAREST) for f in loop]


def main() -> None:
    if not METAL_SHEET.exists():
        raise SystemExit(f"missing Metal Man sheet: {METAL_SHEET}")

    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "Contents.json").write_text(
        json.dumps({"info": {"author": "xcode", "version": 1}}, indent=2) + "\n"
    )

    for path in list(OUT.iterdir()):
        if path.is_dir() and path.name.endswith(".imageset"):
            for child in path.iterdir():
                child.unlink()
            path.rmdir()

    for i, img in enumerate(build_loop(METAL_SHEET)):
        name = f"metal-man_{i:02d}"
        write_imageset(OUT / f"{name}.imageset", img, name)

    (OUT.parent / "sprite-manifest.json").write_text(
        json.dumps(
            {
                "characters": [
                    {
                        "id": "metal-man",
                        "name": "Metal Man",
                        "frameCount": FRAME_COUNT,
                        "source": "sheet",
                        "loop": "walk×4 → ready → jump → air-throw×2 → land → idle",
                    }
                ],
                "frameCount": FRAME_COUNT,
                "framesPerSecond": 8,
            },
            indent=2,
        )
        + "\n"
    )
    print(f"Wrote {FRAME_COUNT} Metal Man frames to {OUT}")


if __name__ == "__main__":
    main()
