#!/usr/bin/env python3
"""Build Metal Man widget sprite assets from the authentic Mega Man 2 sheet.

Source: Shared/MegaManWidget/SourcesSheets/metal-man.gif
Output: Shared/MegaManWidget/Assets.xcassets/metal-man_{00…07}.imageset
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
    if not METAL_SHEET.exists():
        raise SystemExit(f"missing Metal Man sheet: {METAL_SHEET}")

    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "Contents.json").write_text(
        json.dumps({"info": {"author": "xcode", "version": 1}}, indent=2) + "\n"
    )

    # Drop any leftover non-Metal-Man imagesets from earlier placeholder art.
    for path in OUT.iterdir():
        if path.is_dir() and path.name.endswith(".imageset") and not path.name.startswith("metal-man_"):
            for child in path.iterdir():
                child.unlink()
            path.rmdir()

    for i, img in enumerate(build_metal_man_loop(METAL_SHEET)):
        name = f"metal-man_{i:02d}"
        write_imageset(OUT / f"{name}.imageset", img, name)

    manifest = OUT.parent / "sprite-manifest.json"
    manifest.write_text(
        json.dumps(
            {
                "characters": [
                    {"id": "metal-man", "name": "Metal Man", "frameCount": 8, "source": "sheet"}
                ],
                "frameCount": 8,
            },
            indent=2,
        )
        + "\n"
    )
    print(f"Wrote Metal Man loop to {OUT}")


if __name__ == "__main__":
    main()
