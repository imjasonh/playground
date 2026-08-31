#!/usr/bin/env python3
"""Render printable Tank / APC / Infantry unit boards (one page each)."""

from __future__ import annotations

from pathlib import Path

from reportlab.lib.colors import Color, white
from reportlab.lib.pagesizes import letter
from reportlab.lib.units import inch
from reportlab.pdfgen import canvas

OUT_DEFAULT = Path(__file__).resolve().parents[1] / "docs" / "unit-boards.pdf"

# Shared rhythm.
BOX = 0.30 * inch
BOX_GAP = 0.08 * inch
ROW = BOX + 0.16 * inch  # vertical pitch between checkbox rows
COL = 1.35 * inch  # labeled-checkbox column pitch
INK = Color(0.12, 0.10, 0.08)
MUTED = Color(0.40, 0.38, 0.34)
RULE = Color(0.28, 0.26, 0.24)
PAGE_BG = Color(0.96, 0.94, 0.90)
PANEL_BG = white


def checkbox(c: canvas.Canvas, x: float, y: float) -> None:
    c.setStrokeColor(RULE)
    c.setFillColor(PANEL_BG)
    c.setLineWidth(1.2)
    c.rect(x, y, BOX, BOX, fill=1, stroke=1)


def text_mid(y: float, size: float = 10) -> float:
    return y + (BOX - size) * 0.5 + 0.5


def draw_label(c: canvas.Canvas, x: float, y: float, text: str, size: float = 10) -> None:
    c.setFillColor(INK)
    c.setFont("Helvetica", size)
    c.drawString(x, text_mid(y, size), text)


def labeled_box(c: canvas.Canvas, x: float, y: float, text: str) -> None:
    checkbox(c, x, y)
    draw_label(c, x + BOX + 5, y, text)


def activated_top_right(c: canvas.Canvas, right: float, y: float) -> None:
    """Right-align Activated so the label ends at `right`."""
    label = "Activated"
    tw = c.stringWidth(label, "Helvetica", 10)
    labeled_box(c, right - BOX - 5 - tw, y, label)


def underline(c: canvas.Canvas, x: float, y: float, w: float) -> None:
    c.setStrokeColor(RULE)
    c.setLineWidth(1.0)
    c.line(x, y, x + w, y)


def field(c: canvas.Canvas, x: float, y: float, w: float, label: str) -> None:
    """Write-in field: label above underline at y."""
    c.setFillColor(MUTED)
    c.setFont("Helvetica", 8)
    c.drawString(x, y + 8, label)
    underline(c, x, y, w)


def section_head(c: canvas.Canvas, x: float, y: float, title: str, width: float) -> float:
    """
    Section title. Returns y for the *bottom* of the first content row
    (checkbox baseline), with a fixed clear band under the title.
    """
    c.setFillColor(INK)
    c.setFont("Helvetica-Bold", 9)
    c.drawString(x, y, title.upper())
    # Soft rule under the title.
    c.setStrokeColor(Color(0.75, 0.72, 0.68))
    c.setLineWidth(0.6)
    c.line(x, y - 3, x + width, y - 3)
    # Title baseline → rule → 6pt air → checkbox top → BOX down to baseline.
    return y - 3 - 6 - BOX


def hull_track(c: canvas.Canvas, x: float, y: float, n: int) -> float:
    """Hull label + n boxes. Returns x just after the track."""
    draw_label(c, x, y, "Hull")
    bx = x + 28
    for _ in range(n):
        checkbox(c, bx, y)
        bx += BOX + BOX_GAP
    return bx


def flag_row(c: canvas.Canvas, x: float, y: float, labels: list[str], pitch: float = COL) -> None:
    for i, text in enumerate(labels):
        labeled_box(c, x + i * pitch, y, text)


def upgrade_grid(
    c: canvas.Canvas, x: float, y: float, items: list[str], cols: int, pitch: float
) -> float:
    """Draw grid; return baseline of the last row."""
    last = y
    for i, text in enumerate(items):
        col = i % cols
        row = i // cols
        yy = y - row * ROW
        labeled_box(c, x + col * pitch, yy, text)
        last = yy
    return last


def paint_page_bg(c: canvas.Canvas) -> None:
    w, h = letter
    c.setFillColor(PAGE_BG)
    c.rect(0, 0, w, h, fill=1, stroke=0)


def panel(c: canvas.Canvas, x: float, y: float, w: float, h: float) -> None:
    c.setStrokeColor(RULE)
    c.setFillColor(PANEL_BG)
    c.setLineWidth(1.4)
    c.roundRect(x, y, w, h, 4, fill=1, stroke=1)


def draw_tank_page(c: canvas.Canvas) -> None:
    paint_page_bg(c)
    page_w, page_h = letter
    margin = 0.5 * inch
    panel_x = margin
    panel_y = margin
    panel_w = page_w - 2 * margin
    panel_h = page_h - 2 * margin
    panel(c, panel_x, panel_y, panel_w, panel_h)

    x = panel_x + 0.28 * inch
    width = panel_w - 0.56 * inch
    right = x + width
    y = panel_y + panel_h - 0.38 * inch

    c.setFillColor(INK)
    c.setFont("Helvetica-Bold", 18)
    c.drawString(x, y, "Tank")
    activated_top_right(c, right, y - 4)
    y -= 0.42 * inch

    field(c, x, y, width, "Name")
    y -= 0.48 * inch

    # Loadout stats on an even 7-column grid.
    y = section_head(c, x, y, "Loadout", width)
    # Stat underlines sit on the same baseline as checkbox rows would.
    stats = ["F", "S", "R", "Move", "AP", "Rng", "Acc"]
    stat_pitch = width / len(stats)
    for i, label in enumerate(stats):
        field(c, x + i * stat_pitch, y + 2, stat_pitch - 0.12 * inch, label)
    y -= 0.40 * inch

    upgrades = [
        "Engine",
        "Optics",
        "Barrel",
        "Anti-infantry",
        "Air Strike",
        "Smoke",
        "Medkit",
        "Lieutenant",
        "HE",
    ]
    up_pitch = width / 3
    y = upgrade_grid(c, x, y, upgrades, cols=3, pitch=up_pitch)
    y -= ROW + 0.18 * inch

    # Battle — hull alone, then status flags.
    y = section_head(c, x, y, "Battle", width)
    hull_track(c, x, y, 4)
    y -= ROW
    flag_row(c, x, y, ["Fire", "Disabled"], pitch=1.25 * inch)
    y -= ROW + 0.16 * inch

    # Gun: breech + spent as two left-labeled rows (same pattern as Hull).
    y = section_head(c, x, y, "Gun", width)
    label_col = 0.72 * inch
    c.setFillColor(MUTED)
    c.setFont("Helvetica", 9)
    c.drawString(x, text_mid(y, 9), "Breech")
    flag_row(c, x + label_col, y, ["Empty", "AT", "HE"], pitch=1.20 * inch)
    y -= ROW
    c.setFillColor(MUTED)
    c.setFont("Helvetica", 9)
    c.drawString(x, text_mid(y, 9), "Spent")
    flag_row(c, x + label_col, y, ["Smoke", "Air Strike", "Medkit"], pitch=1.55 * inch)
    y -= ROW + 0.20 * inch

    # Crew — custom header band so W/K/Abl never sit on the section rule.
    c.setFillColor(INK)
    c.setFont("Helvetica-Bold", 9)
    c.drawString(x, y, "CREW")
    c.setStrokeColor(Color(0.75, 0.72, 0.68))
    c.setLineWidth(0.6)
    c.line(x, y - 3, x + width, y - 3)
    wx = x + 1.55 * inch
    kx = wx + 0.70 * inch
    ax = kx + 0.70 * inch
    c.setFillColor(MUTED)
    c.setFont("Helvetica", 8)
    c.drawCentredString(wx + BOX / 2, y - 16, "W")
    c.drawCentredString(kx + BOX / 2, y - 16, "K")
    c.drawCentredString(ax + BOX / 2, y - 16, "Abl")
    y = y - 16 - 4 - BOX

    for role, ability in (
        ("Commander", "Booming Voice"),
        ("Driver", "Move move move!"),
        ("Gunner", "Snapshot"),
        ("Loader", "Quick Load"),
        ("Lieutenant", None),
    ):
        draw_label(c, x, y, role)
        checkbox(c, wx, y)
        checkbox(c, kx, y)
        checkbox(c, ax, y)
        if role == "Lieutenant":
            c.setFillColor(MUTED)
            c.setFont("Helvetica", 8)
            c.drawString(ax + BOX + 8, text_mid(y, 8), "covers")
            underline(c, ax + BOX + 44, y + 2, 1.6 * inch)
        else:
            c.setFillColor(MUTED)
            c.setFont("Helvetica", 8)
            c.drawString(ax + BOX + 8, text_mid(y, 8), ability)
        y -= ROW

    c.showPage()


def draw_apc_card(c: canvas.Canvas, left: float, bottom: float, card_w: float, card_h: float) -> None:
    panel(c, left, bottom, card_w, card_h)
    pad = 0.22 * inch
    x = left + pad
    width = card_w - 2 * pad
    right = x + width
    y = bottom + card_h - 0.30 * inch

    c.setFillColor(INK)
    c.setFont("Helvetica-Bold", 14)
    c.drawString(x, y, "APC")
    activated_top_right(c, right, y - 2)
    y -= 0.36 * inch

    field(c, x, y, width, "Name")
    y -= 0.40 * inch

    y = section_head(c, x, y, "Loadout", width)
    stats = ["F", "S", "R", "Move", "AP", "Anti-infantry"]
    pitch = width / len(stats)
    for i, label in enumerate(stats):
        field(c, x + i * pitch, y + 2, pitch - 0.10 * inch, label)
    y -= 0.34 * inch

    flag_row(c, x, y, ["Engine", "Smoke"], pitch=1.25 * inch)
    y -= ROW + 0.12 * inch

    y = section_head(c, x, y, "Battle", width)
    hull_track(c, x, y, 2)
    y -= ROW
    flag_row(c, x, y, ["Fire", "Disabled"], pitch=1.25 * inch)
    y -= ROW
    labeled_box(c, x, y, "Smoke spent")


def draw_apc_page(c: canvas.Canvas) -> None:
    """Two APC cards on a letter page (cut apart)."""
    paint_page_bg(c)
    page_w, page_h = letter
    card_w = 5.2 * inch
    card_h = 4.0 * inch
    gap = 0.28 * inch
    total_h = 2 * card_h + gap
    left = (page_w - card_w) / 2
    bottom0 = (page_h - total_h) / 2
    draw_apc_card(c, left, bottom0 + card_h + gap, card_w, card_h)
    draw_apc_card(c, left, bottom0, card_w, card_h)
    c.showPage()


def draw_infantry_card(c: canvas.Canvas, left: float, bottom: float, card_w: float, card_h: float) -> None:
    panel(c, left, bottom, card_w, card_h)
    pad = 0.20 * inch
    x = left + pad
    inner_w = card_w - 2 * pad
    right = x + inner_w

    y_title = bottom + card_h - pad - 12
    y_name = bottom + (card_h / 2) - 4

    c.setFillColor(INK)
    c.setFont("Helvetica-Bold", 13)
    c.drawString(x, y_title, "Infantry")
    activated_top_right(c, right, y_title - 2)

    field(c, x, y_name, inner_w, "Name")


def draw_infantry_page(c: canvas.Canvas) -> None:
    """2×4 infantry cards filling the letter page for cutting."""
    paint_page_bg(c)
    page_w, page_h = letter
    margin = 0.4 * inch
    cols, rows = 2, 4
    gap_x = 0.16 * inch
    gap_y = 0.14 * inch
    card_w = (page_w - 2 * margin - (cols - 1) * gap_x) / cols
    card_h = (page_h - 2 * margin - (rows - 1) * gap_y) / rows
    origin_x = margin
    origin_y = margin
    for row in range(rows):
        for col in range(cols):
            left = origin_x + col * (card_w + gap_x)
            bottom = origin_y + (rows - 1 - row) * (card_h + gap_y)
            draw_infantry_card(c, left, bottom, card_w, card_h)
    c.showPage()


def render(path: Path) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    c = canvas.Canvas(str(path), pagesize=letter)
    c.setTitle("Tank Commander unit boards")
    c.setAuthor("playground/tank-commander")
    draw_tank_page(c)
    draw_apc_page(c)
    draw_infantry_page(c)
    c.save()
    return path


if __name__ == "__main__":
    import sys

    out = Path(sys.argv[1]) if len(sys.argv) > 1 else OUT_DEFAULT
    print(render(out))
