#!/usr/bin/env python3
"""Render flat-top vs pointy-top board comparison PNGs for Tank Commander."""

from __future__ import annotations

import math
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont

OUT = Path("/opt/cursor/artifacts")
OUT.mkdir(parents=True, exist_ok=True)

# Colors
BG = (246, 242, 232)
OPEN = (214, 206, 184)
FOREST = (74, 120, 74)
BUILDING = (120, 108, 96)
MUD = (148, 120, 72)
RUBBLE = (160, 148, 132)
RED_ZONE = (210, 92, 78)
BLUE_ZONE = (78, 118, 186)
FLAG = (240, 210, 60)
INK = (36, 32, 28)
LABEL = (60, 54, 48)
GRID = (90, 82, 70)


def font(size: int):
    for path in (
        "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
        "/usr/share/fonts/truetype/liberation/LiberationSans-Regular.ttf",
    ):
        try:
            return ImageFont.truetype(path, size)
        except OSError:
            continue
    return ImageFont.load_default()


def hex_corners_flat(cx: float, cy: float, size: float) -> list[tuple[float, float]]:
    # Flat-top: point-sided (points at N/S? No — flat on top means points at E/W).
    # Flat-top vertices at 0°, 60°, ... starting from east tip.
    return [
        (
            cx + size * math.cos(math.radians(60 * i)),
            cy + size * math.sin(math.radians(60 * i)),
        )
        for i in range(6)
    ]


def hex_corners_pointy(cx: float, cy: float, size: float) -> list[tuple[float, float]]:
    # Pointy-top: flat-sided (flats at E/W). Vertices start at 30°.
    return [
        (
            cx + size * math.cos(math.radians(60 * i + 30)),
            cy + size * math.sin(math.radians(60 * i + 30)),
        )
        for i in range(6)
    ]


def flat_centers(w: int, h: int, size: float, origin: tuple[float, float]):
    """Odd-q flat-top pixel centers."""
    ox, oy = origin
    out = {}
    for col in range(w):
        for row in range(h):
            x = ox + size * 1.5 * col
            y = oy + size * math.sqrt(3) * (row + 0.5 * (col & 1))
            out[(col, row)] = (x, y)
    return out


def pointy_centers(w: int, h: int, size: float, origin: tuple[float, float]):
    """Odd-r pointy-top pixel centers."""
    ox, oy = origin
    out = {}
    for col in range(w):
        for row in range(h):
            x = ox + size * math.sqrt(3) * (col + 0.5 * (row & 1))
            y = oy + size * 1.5 * row
            out[(col, row)] = (x, y)
    return out


def draw_board(
    draw: ImageDraw.ImageDraw,
    centers: dict,
    corners_fn,
    size: float,
    w: int,
    h: int,
    depth: int,
    flag_row: int,
    title: str,
    subtitle: str,
    fill_fn,
):
    f_title = font(28)
    f_sub = font(16)
    f_tiny = font(12)
    # Title above first hex
    xs = [c[0] for c in centers.values()]
    ys = [c[1] for c in centers.values()]
    left, top = min(xs) - size, min(ys) - size - 56
    draw.text((left, top), title, fill=INK, font=f_title)
    draw.text((left, top + 32), subtitle, fill=LABEL, font=f_sub)

    for (col, row), (cx, cy) in centers.items():
        fill = fill_fn(col, row, depth, w, h, flag_row)
        pts = corners_fn(cx, cy, size * 0.95)
        draw.polygon(pts, fill=fill, outline=GRID)
        if (col == 0 and row == flag_row) or (col == w - 1 and row == flag_row):
            r = size * 0.28
            draw.ellipse((cx - r, cy - r, cx + r, cy + r), fill=FLAG, outline=INK)

    # Legend labels
    red_c = centers[(0, h // 2)]
    blue_c = centers[(w - 1, h // 2)]
    draw.text((red_c[0] - size * 0.4, red_c[1] + size * 1.1), "RED", fill=RED_ZONE, font=f_tiny)
    draw.text((blue_c[0] - size * 0.5, blue_c[1] + size * 1.1), "BLUE", fill=BLUE_ZONE, font=f_tiny)


def zone_fill(col, row, depth, w, h, flag_row):
    if col < depth:
        return RED_ZONE if (col + row) % 2 == 0 else (190, 80, 68)
    if col >= w - depth:
        return BLUE_ZONE if (col + row) % 2 == 0 else (68, 108, 170)
    # Midfield texture
    if (col + row) % 5 == 0:
        return FOREST
    if (col * 3 + row) % 11 == 0:
        return BUILDING
    if (col + row * 2) % 13 == 0:
        return MUD
    return OPEN


def render_comparison():
    w, h, depth = 18, 12, 3
    flag_row = 6
    size = 18.0
    # Flat board footprint
    flat_w = int(size * 1.5 * (w - 1) + 2 * size) + 80
    flat_h = int(size * math.sqrt(3) * (h + 0.5) + 2 * size) + 100
    # Pointy board footprint
    pointy_w = int(size * math.sqrt(3) * (w + 0.5) + 2 * size) + 80
    pointy_h = int(size * 1.5 * (h - 1) + 2 * size) + 100

    panel_w = max(flat_w, pointy_w) + 40
    panel_h = max(flat_h, pointy_h) + 40
    img = Image.new("RGB", (panel_w * 2 + 40, panel_h + 120), BG)
    draw = ImageDraw.Draw(img)
    f_big = font(34)
    draw.text((40, 24), "Tank Commander boards: same E/W layout, new hex orientation", fill=INK, font=f_big)

    # Left: OLD pointy-top (flat-sided)
    left_origin = (60, 130)
    pointy = pointy_centers(w, h, size, left_origin)
    draw_board(
        draw,
        pointy,
        hex_corners_pointy,
        size,
        w,
        h,
        depth,
        flag_row,
        "Before — pointy-top (flat-sided)",
        "E–W race distances chiral by row (Red had more optimal hexes)",
        zone_fill,
    )

    # Right: NEW flat-top (point-sided)
    right_origin = (panel_w + 60, 130)
    flat = flat_centers(w, h, size, right_origin)
    draw_board(
        draw,
        flat,
        hex_corners_flat,
        size,
        w,
        h,
        depth,
        flag_row,
        "After — flat-top (point-sided)",
        "E–W race distances symmetric (every row length 15)",
        zone_fill,
    )

    path = OUT / "board-orientation-before-after.png"
    img.save(path)
    print(path)
    return path


def render_single(kind: str, orientation: str):
    """Render one labeled 18×12 (or 9×12) board in the given orientation."""
    if kind == "skirmish":
        w, h, depth = 9, 12, 2
    else:
        w, h, depth = 18, 12, 3
    flag_row = 6
    size = 22.0 if kind == "skirmish" else 18.0
    if orientation == "flat":
        centers_fn, corners_fn = flat_centers, hex_corners_flat
        title = f"{kind.title()} — flat-top (point-sided)"
        sub = "Red west · Blue east · odd-q columns×rows"
        pw = int(size * 1.5 * (w - 1) + 2 * size) + 100
        ph = int(size * math.sqrt(3) * (h + 0.5) + 2 * size) + 140
    else:
        centers_fn, corners_fn = pointy_centers, hex_corners_pointy
        title = f"{kind.title()} — pointy-top (flat-sided, old)"
        sub = "Same E/W nomenclature; chiral race axis"
        pw = int(size * math.sqrt(3) * (w + 0.5) + 2 * size) + 100
        ph = int(size * 1.5 * (h - 1) + 2 * size) + 140

    img = Image.new("RGB", (pw, ph), BG)
    draw = ImageDraw.Draw(img)
    centers = centers_fn(w, h, size, (50, 100))
    draw_board(draw, centers, corners_fn, size, w, h, depth, flag_row, title, sub, zone_fill)
    path = OUT / f"board-{kind}-{orientation}.png"
    img.save(path)
    print(path)
    return path


if __name__ == "__main__":
    render_comparison()
    for kind in ("skirmish", "combined", "capture"):
        for orient in ("pointy", "flat"):
            render_single(kind, orient)
