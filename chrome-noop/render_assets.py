#!/usr/bin/env python3
"""Render toolbar icons, the store icon, and the 1280x800 screenshot.

Requires Pillow. The checked-in PNGs are the files the zip and the
dashboard listing use. Run this only to regenerate them.
"""

import os

from PIL import Image, ImageDraw, ImageFont

HERE = os.path.dirname(os.path.abspath(__file__))
ICON_SIZES = (16, 32, 48, 128)
FONT = "/usr/share/fonts/truetype/macos/Inter-Regular.ttf"
BLUE = (26, 115, 232, 255)
WHITE = (255, 255, 255, 255)


def render_icon(size):
    image = Image.new("RGBA", (size, size), (0, 0, 0, 0))
    draw = ImageDraw.Draw(image)
    pad = max(1, round(size * 0.06))
    draw.ellipse((pad, pad, size - 1 - pad, size - 1 - pad), fill=BLUE)
    bar_h = max(2, round(size * 0.14))
    bar_w = round(size * 0.46)
    x0 = (size - bar_w) // 2
    y0 = (size - bar_h) // 2
    radius = max(1, bar_h // 2)
    draw.rounded_rectangle(
        (x0, y0, x0 + bar_w - 1, y0 + bar_h - 1),
        radius=radius,
        fill=WHITE,
    )
    return image


def render_store_icon():
    # Chrome Web Store wants a 128px image whose mark is 96px, centered.
    art = render_icon(96)
    image = Image.new("RGBA", (128, 128), (0, 0, 0, 0))
    image.paste(art, (16, 16), art)
    return image


def render_screenshot(icon):
    image = Image.new("RGB", (1280, 800), (241, 243, 244))
    draw = ImageDraw.Draw(image)
    card = (400, 280, 880, 520)
    draw.rounded_rectangle(card, radius=12, fill=(255, 255, 255))
    thumb = icon.resize((64, 64), Image.Resampling.LANCZOS)
    image.paste(thumb, (440, 360), thumb)
    font = ImageFont.truetype(FONT, 22)
    draw.text(
        (524, 376),
        "This extension opens this popup.\nIt requests no permissions\nand collects no data.",
        fill=(26, 26, 26),
        font=font,
        spacing=6,
    )
    return image


def main():
    icons_dir = os.path.join(HERE, "icons")
    os.makedirs(icons_dir, exist_ok=True)
    os.makedirs(os.path.join(HERE, "store"), exist_ok=True)
    icon128 = None
    for size in ICON_SIZES:
        icon = render_icon(size)
        icon.save(os.path.join(icons_dir, f"{size}.png"))
        if size == 128:
            icon128 = icon
    screenshot = render_screenshot(icon128)
    screenshot.save(os.path.join(HERE, "store", "screenshot.png"), "PNG")
    render_store_icon().save(os.path.join(HERE, "store", "icon-128.png"))


if __name__ == "__main__":
    main()
