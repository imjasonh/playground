#!/usr/bin/env python3
"""Render toolbar icons and the store icon.

Requires Pillow. The checked-in PNGs are the files the zip and the
dashboard listing use. The store screenshots are captures of Chrome.
Run capture_screenshot.py to replace those.
"""

import os

from PIL import Image, ImageDraw

HERE = os.path.dirname(os.path.abspath(__file__))
ICON_SIZES = (16, 32, 48, 128)
BLUE = (26, 115, 232, 255)
WHITE = (255, 255, 255, 255)


def render_icon(size):
    image = Image.new("RGBA", (size, size), (0, 0, 0, 0))
    draw = ImageDraw.Draw(image)
    radius = max(2, size // 5)
    draw.rounded_rectangle((0, 0, size - 1, size - 1), radius=radius, fill=BLUE)
    inset = max(2, size // 6)
    tab_h = max(3, size // 5)
    gap = max(1, size // 16)
    back_inset = inset + max(1, size // 12)
    top = inset + max(1, size // 12)
    radius_tab = max(1, tab_h // 3)
    draw.rounded_rectangle(
        (back_inset, top, size - 1 - back_inset, top + tab_h),
        radius=radius_tab,
        fill=(255, 255, 255, 170),
    )
    front_top = top + tab_h + gap
    draw.rounded_rectangle(
        (inset, front_top, size - 1 - inset, front_top + tab_h),
        radius=radius_tab,
        fill=WHITE,
    )
    return image


def render_store_icon():
    # The store icon is 128px. The mark is 96px, centered, with 16px of padding.
    art = render_icon(96)
    image = Image.new("RGBA", (128, 128), (0, 0, 0, 0))
    image.paste(art, (16, 16), art)
    return image


def main():
    icons_dir = os.path.join(HERE, "icons")
    os.makedirs(icons_dir, exist_ok=True)
    os.makedirs(os.path.join(HERE, "store"), exist_ok=True)
    for size in ICON_SIZES:
        render_icon(size).save(os.path.join(icons_dir, f"{size}.png"))
    render_store_icon().save(os.path.join(HERE, "store", "icon-128.png"))


if __name__ == "__main__":
    main()
