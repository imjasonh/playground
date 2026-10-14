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
FONT_MEDIUM = "/usr/share/fonts/truetype/macos/Inter-Medium.ttf"
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


def render_screenshot(icon):
    image = Image.new("RGB", (1280, 800), (232, 234, 237))
    draw = ImageDraw.Draw(image)
    window = (80, 64, 1200, 736)
    draw.rounded_rectangle(window, radius=16, fill=(255, 255, 255))
    draw.rounded_rectangle((80, 64, 1200, 168), radius=16, fill=(222, 225, 230))
    draw.rectangle((80, 140, 1200, 168), fill=(222, 225, 230))

    titles = ("Example", "Example", "Mail")
    active = 0
    font = ImageFont.truetype(FONT, 18)
    x = 104
    for index, title in enumerate(titles):
        width = 168
        box = (x, 96, x + width, 168)
        fill = (255, 255, 255) if index == active else (206, 210, 214)
        draw.rounded_rectangle(box, radius=10, fill=fill)
        draw.rectangle((x, 140, x + width, 168), fill=fill)
        draw.text((x + 16, 114), title, fill=(32, 33, 36), font=font)
        x += width + 8

    draw.rectangle((80, 168, 1200, 228), fill=(255, 255, 255))
    draw.text((120, 186), "https://example.com/notes", fill=(95, 99, 104), font=font)

    thumb = icon.resize((28, 28), Image.Resampling.LANCZOS)
    image.paste(thumb, (1108, 182), thumb)
    badge_font = ImageFont.truetype(FONT_MEDIUM, 14)
    badge = (1124, 196, 1148, 218)
    draw.rounded_rectangle(badge, radius=11, fill=(23, 78, 166))
    draw.text((1131, 198), "1", fill=(255, 255, 255), font=badge_font)

    body = ImageFont.truetype(FONT, 28)
    draw.text(
        (120, 280),
        "Click the toolbar button to close extra tabs\nthat share a URL. The badge shows how many\ntabs the click will close.",
        fill=(32, 33, 36),
        font=body,
        spacing=10,
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
    render_screenshot(icon128).save(os.path.join(HERE, "store", "screenshot.png"), "PNG")
    render_store_icon().save(os.path.join(HERE, "store", "icon-128.png"))


if __name__ == "__main__":
    main()
