#!/usr/bin/env python3
"""Render printable Tank / APC / Infantry unit boards (one page each)."""

from __future__ import annotations

from pathlib import Path

from reportlab.lib.colors import Color, white
from reportlab.lib.pagesizes import letter
from reportlab.lib.units import inch
from reportlab.pdfgen import canvas

OUT_DEFAULT = Path(__file__).resolve().parents[1] / "docs" / "unit-boards.pdf"

BOX = 0.28 * inch
GAP = 0.10 * inch
ROW = BOX + 14  # checkbox row pitch
RULE = Color(0.22, 0.20, 0.18)
MUTED = Color(0.38, 0.36, 0.32)
FILL = Color(0.96, 0.94, 0.90)
INK = Color(0.12, 0.10, 0.08)


def checkbox(c: canvas.Canvas, x: float, y: float, size: float = BOX) -> None:
    c.setStrokeColor(RULE)
    c.setFillColor(white)
    c.setLineWidth(1.25)
    c.rect(x, y, size, size, fill=1, stroke=1)


def label_y(box_y: float, font_size: float = 10) -> float:
    return box_y + (BOX - font_size) / 2 + 0.5


def labeled_box(c: canvas.Canvas, x: float, y: float, text: str, font_size: float = 10) -> float:
    checkbox(c, x, y)
    c.setFillColor(INK)
    c.setFont("Helvetica", font_size)
    tx = x + BOX + 5
    c.drawString(tx, label_y(y, font_size), text)
    return tx + c.stringWidth(text, "Helvetica", font_size)


def underline(c: canvas.Canvas, x: float, y: float, w: float) -> None:
    c.setStrokeColor(RULE)
    c.setLineWidth(1)
    c.line(x, y, x + w, y)


def field(c: canvas.Canvas, x: float, y: float, w: float, text: str) -> None:
    """Write-in field. `y` is the underline."""
    c.setFillColor(MUTED)
    c.setFont("Helvetica", 8)
    c.drawString(x, y + 9, text)
    underline(c, x, y, w)


def section(c: canvas.Canvas, x: float, y: float, title: str, width: float) -> float:
    """
    Draw section title + rule. Return the y where a checkbox bottom should sit
    so the box top clears the rule by 8pt.
    """
    c.setFillColor(INK)
    c.setFont("Helvetica-Bold", 9)
    c.drawString(x, y, title.upper())
    rule_y = y - 5
    c.setStrokeColor(MUTED)
    c.setLineWidth(0.7)
    c.line(x, rule_y, x + width, rule_y)
    # Clearance under rule, then room for a full checkbox above the returned y.
    return rule_y - 8 - BOX


def page_shell(c: canvas.Canvas, title: str) -> tuple[float, float, float]:
    w, h = letter
    m = 0.55 * inch
    c.setFillColor(FILL)
    c.rect(0, 0, w, h, fill=1, stroke=0)
    c.setStrokeColor(RULE)
    c.setLineWidth(1.5)
    c.rect(m, m, w - 2 * m, h - 2 * m, fill=0, stroke=1)
    left = m + 18
    width = w - 2 * m - 36
    top = h - m - 28
    c.setFillColor(INK)
    c.setFont("Helvetica-Bold", 18)
    c.drawString(left, top, title)
    return left, top - 34, width


def card_shell(
    c: canvas.Canvas, title: str, card_w: float, card_h: float
) -> tuple[float, float, float]:
    w, h = letter
    c.setFillColor(FILL)
    c.rect(0, 0, w, h, fill=1, stroke=0)
    pad = 16
    cx = (w - card_w) / 2
    cy = (h - card_h) / 2
    c.setStrokeColor(RULE)
    c.setLineWidth(1.5)
    c.setFillColor(white)
    c.roundRect(cx, cy, card_w, card_h, 6, fill=1, stroke=1)
    left = cx + pad
    width = card_w - 2 * pad
    top = cy + card_h - 22
    c.setFillColor(INK)
    c.setFont("Helvetica-Bold", 14)
    c.drawString(left, top, title)
    return left, top - 26, width


def tick_grid(
    c: canvas.Canvas,
    x: float,
    y: float,
    items: list[str],
    cols: int,
    col_w: float,
) -> float:
    last = y
    for i, text in enumerate(items):
        col = i % cols
        row = i // cols
        yy = y - row * ROW
        labeled_box(c, x + col * col_w, yy, text)
        last = yy
    return last


def hull_boxes(c: canvas.Canvas, x: float, y: float, n: int) -> float:
    c.setFillColor(INK)
    c.setFont("Helvetica", 10)
    c.drawString(x, label_y(y), "Hull")
    bx = x + 30
    for _ in range(n):
        checkbox(c, bx, y)
        bx += BOX + GAP
    return bx + 8


def status_flags(c: canvas.Canvas, x: float, y: float, labels: list[str], col_w: float = 1.25 * inch) -> None:
    for i, text in enumerate(labels):
        labeled_box(c, x + i * col_w, y, text)


def draw_tank_page(c: canvas.Canvas) -> None:
    x, y, width = page_shell(c, "Tank")

    field(c, x, y, 3.0 * inch, "Name")
    field(c, x + 3.2 * inch, y, 1.1 * inch, "Side")
    field(c, x + 4.5 * inch, y, 1.2 * inch, "Pts")
    y -= 40

    y = section(c, x, y, "Loadout", width)
    # Stat write-ins sit on the checkbox baseline row.
    field(c, x, y + 2, 0.6 * inch, "F")
    field(c, x + 0.8 * inch, y + 2, 0.6 * inch, "S")
    field(c, x + 1.6 * inch, y + 2, 0.6 * inch, "R")
    field(c, x + 2.4 * inch, y + 2, 0.6 * inch, "Move")
    field(c, x + 3.2 * inch, y + 2, 0.5 * inch, "AP")
    field(c, x + 3.9 * inch, y + 2, 0.6 * inch, "Rng")
    field(c, x + 4.7 * inch, y + 2, 0.6 * inch, "Acc")
    y -= 34

    y = tick_grid(
        c,
        x,
        y,
        ["Engine", "Optics", "Barrel", "AI", "Air", "Smoke", "Medkit", "LT", "HE"],
        cols=3,
        col_w=width / 3,
    )
    y -= ROW + 10

    y = section(c, x, y, "Battle", width)
    right = hull_boxes(c, x, y, 4)
    status_flags(c, right, y, ["Fire", "Disabled", "Activated"], col_w=1.3 * inch)
    y -= ROW + 6

    y = section(c, x, y, "Breech", width)
    labeled_box(c, x, y, "Empty")
    labeled_box(c, x + 1.2 * inch, y, "AT")
    labeled_box(c, x + 2.1 * inch, y, "HE")
    y -= ROW + 6

    y = section(c, x, y, "Spent", width)
    labeled_box(c, x, y, "Smoke")
    labeled_box(c, x + 1.35 * inch, y, "Air")
    labeled_box(c, x + 2.5 * inch, y, "Medkit")
    y -= ROW + 12

    y = section(c, x, y, "Crew", width)
    # Extra band for column headers between the rule and the first row.
    y -= 14
    wx = x + 1.5 * inch
    kx = x + 2.2 * inch
    ax = x + 2.9 * inch
    c.setFillColor(MUTED)
    c.setFont("Helvetica", 8)
    c.drawCentredString(wx + BOX / 2, y + BOX + 3, "W")
    c.drawCentredString(kx + BOX / 2, y + BOX + 3, "K")
    c.drawCentredString(ax + BOX / 2, y + BOX + 3, "Abl")

    for role in ("Commander", "Driver", "Gunner", "Loader", "Lieutenant"):
        c.setFillColor(INK)
        c.setFont("Helvetica", 10)
        c.drawString(x, label_y(y), role)
        checkbox(c, wx, y)
        checkbox(c, kx, y)
        checkbox(c, ax, y)
        if role == "Lieutenant":
            c.setFillColor(MUTED)
            c.setFont("Helvetica", 8)
            c.drawString(ax + BOX + 10, label_y(y, 8), "covers")
            underline(c, ax + BOX + 46, y + 2, 1.5 * inch)
        y -= ROW

    c.showPage()


def draw_apc_page(c: canvas.Canvas) -> None:
    x, y, width = card_shell(c, "APC", 5.1 * inch, 3.35 * inch)

    field(c, x, y, 2.3 * inch, "Name")
    field(c, x + 2.5 * inch, y, 0.9 * inch, "Side")
    field(c, x + 3.55 * inch, y, 0.85 * inch, "Pts")
    y -= 36

    y = section(c, x, y, "Loadout", width)
    field(c, x, y + 2, 0.55 * inch, "F")
    field(c, x + 0.7 * inch, y + 2, 0.55 * inch, "S")
    field(c, x + 1.4 * inch, y + 2, 0.55 * inch, "R")
    field(c, x + 2.1 * inch, y + 2, 0.55 * inch, "Move")
    field(c, x + 2.8 * inch, y + 2, 0.45 * inch, "AP")
    field(c, x + 3.4 * inch, y + 2, 0.65 * inch, "AI")
    y -= 32

    labeled_box(c, x, y, "Engine")
    labeled_box(c, x + 1.55 * inch, y, "Smoke")
    y -= ROW + 10

    y = section(c, x, y, "Battle", width)
    right = hull_boxes(c, x, y, 2)
    status_flags(c, right, y, ["Fire", "Disabled"], col_w=1.25 * inch)
    y -= ROW + 4
    status_flags(c, x, y, ["Activated", "Smoke spent"], col_w=1.7 * inch)
    c.showPage()


def draw_infantry_page(c: canvas.Canvas) -> None:
    x, y, _width = card_shell(c, "Infantry", 4.2 * inch, 1.35 * inch)

    field(c, x, y, 2.3 * inch, "Name")
    field(c, x + 2.5 * inch, y, 1.1 * inch, "Side")
    y -= 34
    labeled_box(c, x, y, "Activated")
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
