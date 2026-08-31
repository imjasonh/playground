#!/usr/bin/env python3
"""Render printable Tank / APC / Infantry unit boards (one page each)."""

from __future__ import annotations

from pathlib import Path

from reportlab.lib.colors import Color, white
from reportlab.lib.pagesizes import letter
from reportlab.lib.units import inch
from reportlab.pdfgen import canvas

OUT_DEFAULT = Path(__file__).resolve().parents[1] / "docs" / "unit-boards.pdf"

# Checkbox size: readable, easy to tick with dry-erase or pencil.
BOX = 0.32 * inch
BOX_GAP = 0.12 * inch
RULE = Color(0.25, 0.22, 0.18)
MUTED = Color(0.45, 0.42, 0.38)
FILL = Color(0.97, 0.95, 0.90)
ACCENT = Color(0.55, 0.35, 0.22)


def checkbox(c: canvas.Canvas, x: float, y: float, size: float = BOX) -> None:
    c.setStrokeColor(RULE)
    c.setFillColor(white)
    c.setLineWidth(1.4)
    c.rect(x, y, size, size, fill=1, stroke=1)


def labeled_box(c: canvas.Canvas, x: float, y: float, label: str, size: float = BOX) -> None:
    checkbox(c, x, y, size)
    c.setFillColor(RULE)
    c.setFont("Helvetica", 11)
    c.drawString(x + size + 6, y + 4, label)


def line_field(c: canvas.Canvas, x: float, y: float, w: float, label: str) -> None:
    c.setFillColor(MUTED)
    c.setFont("Helvetica", 9)
    c.drawString(x, y + 14, label)
    c.setStrokeColor(RULE)
    c.setLineWidth(1)
    c.line(x, y, x + w, y)


def section_title(c: canvas.Canvas, x: float, y: float, text: str) -> None:
    c.setFillColor(ACCENT)
    c.setFont("Helvetica-Bold", 12)
    c.drawString(x, y, text.upper())


def page_frame(c: canvas.Canvas, title: str) -> tuple[float, float]:
    w, h = letter
    margin = 0.5 * inch
    c.setFillColor(FILL)
    c.rect(0, 0, w, h, fill=1, stroke=0)
    c.setStrokeColor(RULE)
    c.setLineWidth(2)
    c.rect(margin, margin, w - 2 * margin, h - 2 * margin, fill=0, stroke=1)
    c.setFillColor(RULE)
    c.setFont("Helvetica-Bold", 20)
    c.drawString(margin + 14, h - margin - 28, title)
    c.setStrokeColor(RULE)
    c.setLineWidth(1)
    c.line(margin + 14, h - margin - 36, w - margin - 14, h - margin - 36)
    return margin + 14, h - margin - 56


def hull_row(c: canvas.Canvas, x: float, y: float, n: int) -> None:
    c.setFillColor(RULE)
    c.setFont("Helvetica-Bold", 11)
    c.drawString(x, y + 4, "Hull")
    bx = x + 42
    for _ in range(n):
        checkbox(c, bx, y)
        bx += BOX + BOX_GAP


def status_row(c: canvas.Canvas, x: float, y: float) -> None:
    labeled_box(c, x, y, "Fire")
    labeled_box(c, x + 1.35 * inch, y, "Disabled")
    labeled_box(c, x + 3.15 * inch, y, "Activated")


def upgrade_ticks(
    c: canvas.Canvas, x: float, y: float, items: list[str], cols: int = 4
) -> float:
    col_w = 1.7 * inch
    row_h = BOX + 0.18 * inch
    for i, label in enumerate(items):
        col = i % cols
        row = i // cols
        labeled_box(c, x + col * col_w, y - row * row_h, label)
    rows = (len(items) + cols - 1) // cols
    return y - rows * row_h - 6


def draw_tank_page(c: canvas.Canvas) -> None:
    x, y = page_frame(c, "Tank")
    line_field(c, x, y, 3.2 * inch, "Name")
    line_field(c, x + 3.5 * inch, y, 1.2 * inch, "Side")
    line_field(c, x + 5.0 * inch, y, 1.4 * inch, "List pts")
    y -= 0.48 * inch

    section_title(c, x, y, "Armor & stats")
    y -= 0.26 * inch
    line_field(c, x, y, 0.7 * inch, "Front")
    line_field(c, x + 0.95 * inch, y, 0.7 * inch, "Side")
    line_field(c, x + 1.9 * inch, y, 0.7 * inch, "Rear")
    line_field(c, x + 2.9 * inch, y, 0.7 * inch, "Move")
    line_field(c, x + 3.8 * inch, y, 0.55 * inch, "AP")
    line_field(c, x + 4.55 * inch, y, 0.7 * inch, "Range")
    line_field(c, x + 5.45 * inch, y, 0.7 * inch, "Acc TN")
    y -= 0.4 * inch

    y = upgrade_ticks(
        c,
        x,
        y,
        [
            "Engine",
            "Optics",
            "Barrel",
            "AI weapon",
            "Air support",
            "Smoke",
            "Medkit",
            "Lieutenant",
            "HE rounds",
        ],
        cols=3,
    )
    y -= 0.06 * inch

    section_title(c, x, y, "Battle")
    y -= 0.28 * inch
    hull_row(c, x, y, 4)
    y -= 0.4 * inch
    status_row(c, x, y)
    y -= 0.42 * inch

    section_title(c, x, y, "Breech")
    y -= 0.28 * inch
    labeled_box(c, x, y, "Empty")
    labeled_box(c, x + 1.4 * inch, y, "AT")
    labeled_box(c, x + 2.4 * inch, y, "HE")
    y -= 0.42 * inch

    section_title(c, x, y, "Spent")
    y -= 0.28 * inch
    labeled_box(c, x, y, "Smoke")
    labeled_box(c, x + 1.5 * inch, y, "Air")
    labeled_box(c, x + 2.8 * inch, y, "Medkit")
    y -= 0.48 * inch

    section_title(c, x, y, "Crew")
    y -= 0.24 * inch

    c.setFillColor(RULE)
    c.setFont("Helvetica-Bold", 10)
    c.drawString(x + 1.6 * inch, y, "Wounded")
    c.drawString(x + 2.7 * inch, y, "Killed")
    c.drawString(x + 3.7 * inch, y, "Ability")
    y -= 0.08 * inch
    c.setStrokeColor(MUTED)
    c.line(x, y, x + 6.5 * inch, y)
    y -= 0.34 * inch

    rows = [
        ("Commander", "Booming Voice"),
        ("Driver", "Move move move!"),
        ("Gunner", "Snapshot"),
        ("Loader", "Quick Load"),
        ("Lieutenant", "covers: ________"),
    ]
    for role, ability in rows:
        c.setFillColor(RULE)
        c.setFont("Helvetica", 11)
        c.drawString(x, y + 4, role)
        checkbox(c, x + 1.7 * inch, y)
        checkbox(c, x + 2.8 * inch, y)
        checkbox(c, x + 3.85 * inch, y)
        c.setFillColor(MUTED)
        c.setFont("Helvetica", 9)
        c.drawString(x + 3.85 * inch + BOX + 8, y + 4, ability)
        y -= BOX + 0.16 * inch

    c.showPage()


def draw_apc_page(c: canvas.Canvas) -> None:
    x, y = page_frame(c, "APC")
    line_field(c, x, y, 3.2 * inch, "Name")
    line_field(c, x + 3.5 * inch, y, 1.2 * inch, "Side")
    line_field(c, x + 5.0 * inch, y, 1.4 * inch, "List pts")
    y -= 0.55 * inch

    section_title(c, x, y, "Armor & stats")
    y -= 0.28 * inch
    line_field(c, x, y, 0.7 * inch, "Front")
    line_field(c, x + 0.95 * inch, y, 0.7 * inch, "Side")
    line_field(c, x + 1.9 * inch, y, 0.7 * inch, "Rear")
    line_field(c, x + 2.9 * inch, y, 0.7 * inch, "Move")
    line_field(c, x + 3.8 * inch, y, 0.55 * inch, "AP")
    line_field(c, x + 4.55 * inch, y, 0.9 * inch, "AI range")
    y -= 0.5 * inch

    y = upgrade_ticks(c, x, y, ["Engine", "Smoke"], cols=2)
    y -= 0.15 * inch

    section_title(c, x, y, "Battle")
    y -= 0.32 * inch
    hull_row(c, x, y, 2)
    y -= 0.45 * inch
    status_row(c, x, y)
    y -= 0.5 * inch

    section_title(c, x, y, "Spent")
    y -= 0.32 * inch
    labeled_box(c, x, y, "Smoke")
    c.showPage()


def draw_infantry_page(c: canvas.Canvas) -> None:
    w, h = letter
    c.setFillColor(FILL)
    c.rect(0, 0, w, h, fill=1, stroke=0)

    card_w, card_h = 4.25 * inch, 2.6 * inch
    cx = (w - card_w) / 2
    cy = (h - card_h) / 2

    c.setStrokeColor(RULE)
    c.setLineWidth(2)
    c.setFillColor(white)
    c.roundRect(cx, cy, card_w, card_h, 8, fill=1, stroke=1)

    x = cx + 14
    y = cy + card_h - 28
    c.setFillColor(RULE)
    c.setFont("Helvetica-Bold", 14)
    c.drawString(x, y, "Infantry")
    y -= 22
    line_field(c, x, y, 2.4 * inch, "Name")
    line_field(c, x + 2.55 * inch, y, 1.2 * inch, "Side")
    y -= 0.42 * inch

    labeled_box(c, x, y, "Activated")
    y -= 0.42 * inch

    c.setFillColor(RULE)
    c.setFont("Helvetica-Bold", 10)
    c.drawString(x, y, "Actions")
    y -= 14
    c.setFont("Helvetica", 9)
    c.setFillColor(MUTED)
    for line in (
        "Step · Missile (AT or HE) · AI spray",
        "Take cover · Capture · Disarm mine · Mount / Dismount",
    ):
        c.drawString(x, y, line)
        y -= 12

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
