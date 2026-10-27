#!/usr/bin/env python3
"""Generate the subway game's CHR pages, nametables, and band columns.

Usage:

    python3 gen_gfx.py OUT_DIR [MAP_SHAPES_JSON]

Writes OUT_DIR/gfx_chr.ne (tile pages as `sprite` declarations) and
OUT_DIR/gfx_screens.ne (nametables and column strips as const tables
for the Gfx bank). The art is drawn here as ASCII: `.` or `0` is
color 0, and `1`-`3` are colors 1-3 of the cell's palette.

CHR pages:

    0  platform background      2  car interior background
    1  sprites                  3  pause map background
                                4  title background

Every background page starts with the same font at the same tile
numbers, so text code doesn't care which page is mapped.
"""

import json
import math
import os
import sys

sys.path.insert(0, os.path.dirname(__file__))
from font import BULLET_GLYPHS, GLYPHS  # noqa: E402
from gen_data import ROUTES  # noqa: E402

# Route color group -> (sprite palette, bullet color index, NES color
# for sprite palette 3 or 0, dark glyph). Palettes 1 and 2 are fixed;
# palette 3 gets up to two of the other colors per screen. Gray uses
# the player's outline color in palette 0 (black).
GROUP_STYLE = {
    "red": (1, 1, 0, False), "green": (1, 2, 0, False),
    "blue": (2, 1, 0, False), "orange": (2, 2, 0, False),
    "purple": (3, 1, 0x14, False), "lime": (3, 1, 0x2A, False),
    "brown": (3, 1, 0x07, False), "yellow": (3, 1, 0x28, True),
    "gray": (0, 1, 0, True), "shuttle": (0, 1, 0, True),
}

CHARSET = (" ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
           "0123456789-./&'():,!>")
FONT_BASE = 1


def parse(rows):
    """Turn 8 strings into an 8x8 list of color indices."""
    out = []
    for r in rows:
        r = r.replace(".", "0")
        assert len(r) == 8, rows
        out.append([int(c) for c in r])
    assert len(out) == 8, rows
    return out


def chr_bytes(px):
    lo, hi = [], []
    for row in px:
        a = b = 0
        for x, c in enumerate(row):
            if c & 1:
                a |= 0x80 >> x
            if c & 2:
                b |= 0x80 >> x
        lo.append(a)
        hi.append(b)
    return lo + hi


def solid(c):
    return [[c] * 8 for _ in range(8)]


# Band rows 10-11 of the platform use palette 1 (black, gray, white,
# amber) in both nametables, so the side signs' text is amber wherever
# a car lands in the 64-column ring. Palette 0 tiles drawn there are
# recolored: dark gray becomes black, gray and white move down one.
PAL1_FROM_PAL0 = (0, 0, 1, 2)


def to_pal1(page, idx):
    px = [[PAL1_FROM_PAL0[c] for c in row] for row in page.tiles[idx]]
    return page.add(px, None)


def glyph_tile(ch, color=3):
    px = solid(0)
    for y, row in enumerate(GLYPHS[ch]):
        for x, c in enumerate(row):
            if c == "#":
                px[y][x + 1] = color
    return px


class Page:
    """A 256-tile CHR page with dedup by pixel content."""

    def __init__(self, name, first, font=True, reserved=()):
        self.name = name
        self.first = first
        self.reserved = set(reserved)
        self.tiles = [solid(0)] * first
        self.index = {}
        self.names = {}
        if font:
            for ch in CHARSET:
                self.add(glyph_tile(ch), None)

    def add(self, px, name, dedup=True):
        key = tuple(tuple(r) for r in px)
        if dedup and key in self.index:
            idx = self.index[key]
        else:
            while len(self.tiles) in self.reserved:
                self.tiles.append(solid(0))
            idx = len(self.tiles)
            self.tiles.append(px)
            self.index.setdefault(key, idx)
        if name:
            self.names[name] = idx
        assert len(self.tiles) <= 256, f"page {self.name} is full"
        return idx

    def align_run(self, n):
        """Pad so the next n tiles get consecutive numbers."""
        while self.reserved & set(range(len(self.tiles), len(self.tiles) + n)):
            self.tiles.append(solid(0))

    def t(self, name):
        return self.names[name]


class Screen:
    """A 32x30 nametable with a 16x15 palette grid."""

    def __init__(self, fill):
        self.tiles = [[fill] * 32 for _ in range(30)]
        self.pal = [[0] * 16 for _ in range(15)]

    def put(self, x, y, t):
        self.tiles[y][x] = t

    def row(self, y, tiles, x=0):
        for i, t in enumerate(tiles):
            self.tiles[y][x + i] = t

    def fill(self, x0, y0, w, h, t):
        for y in range(y0, y0 + h):
            for x in range(x0, x0 + w):
                self.tiles[y][x] = t

    def palette(self, x0, y0, w, h, p):
        """Set the palette of tile cells x0..x0+w, y0..y0+h (16 px grid)."""
        for y in range(y0 // 2, (y0 + h + 1) // 2):
            for x in range(x0 // 2, (x0 + w + 1) // 2):
                self.pal[y][x] = p

    def text(self, x, y, s):
        for i, ch in enumerate(s):
            self.tiles[y][x + i] = FONT_BASE + CHARSET.index(ch)

    def bytes(self):
        out = [t for row in self.tiles for t in row]
        attrs = []
        for ay in range(8):
            for ax in range(8):
                v = 0
                for q, (dx, dy) in enumerate(((0, 0), (1, 0), (0, 1), (1, 1))):
                    gy = ay * 2 + dy
                    gx = ax * 2 + dx
                    p = self.pal[gy][gx] if gy < 15 else self.pal[14][gx]
                    v |= p << (q * 2)
                attrs.append(v)
        return out + attrs


# --------------------------------------------------------------------
# Platform page (CHR page 0)
# --------------------------------------------------------------------

def build_platform(page):
    T = {}

    def tile(name, rows):
        T[name] = page.add(parse(rows), name)

    tile("black", ["........"] * 8)
    tile("solid1", ["11111111"] * 8)
    tile("solid2", ["22222222"] * 8)
    tile("solid3", ["33333333"] * 8)
    # Ceiling: dark beam with rivets.
    tile("beam", ["11111111", "12111121", "11111111", "11111111",
                  "11111111", "11111111", "22222222", "........"])
    # Mosaic band (palette 2): border rows and a field of small tiles.
    tile("mosaic_top", ["33333333", "31313131", "13131313", "22222222",
                        "21212121", "12121212", "21212121", "12121212"])
    tile("mosaic_bot", ["21212121", "12121212", "21212121", "12121212",
                        "22222222", "13131313", "31313131", "33333333"])
    # Name tablet, rows 6-8: mosaic frame (palette 2) around a white
    # plate. Row 8 is palette 0 and closes the plate above the wall.
    tile("tabf_tl", ["33333333", "31313131", "13131313", "22222222",
                    "21211111", "12213333", "21213333", "12213333"])
    tile("tabf_t", ["33333333", "31313131", "13131313", "22222222",
                   "11111111", "33333333", "33333333", "33333333"])
    tile("tabf_tr", ["33333333", "31313131", "13131313", "22222222",
                    "11111212", "33331221", "33331212", "33331221"])
    tile("tabf_l", ["21213333", "12213333", "21213333", "12213333",
                   "21213333", "12213333", "21213333", "12213333"])
    tile("tabf_r", ["33331212", "33331221", "33331212", "33331221",
                   "33331212", "33331221", "33331212", "33331221"])
    tile("tabf_b", ["33333333", "33333333", "11111111", "33333332",
                   "33333332", "33333332", "33333332", "22222222"])
    tile("tabf_bl", ["....3333", "....3333", "....1111", "33333332",
                    "33333332", "33333332", "33333332", "22222222"])
    tile("tabf_br", ["3333....", "3333....", "1111...2", "33333332",
                    "33333332", "33333332", "33333332", "22222222"])
    # Tablet lettering: black glyphs on the white plate.
    for ch in CHARSET:
        px = solid(3)
        for y, row in enumerate(GLYPHS[ch]):
            for x, c in enumerate(row):
                if c == "#":
                    px[y][x + 1] = 0
        T["tab_" + ch] = page.add(px, None, dedup=False)
    # Upper wall: white glazed tile with gray grout.
    tile("wall", ["33333332", "33333332", "33333332", "33333332",
                  "33333332", "33333332", "33333332", "22222222"])
    # Lower wall in the scrolled band: horizontal detail only, so the
    # wall reads as still while the band scroll moves.
    tile("wall_h", ["33333333", "33333333", "33333333", "22222222",
                    "33333333", "33333333", "33333333", "22222222"])
    T["wall_h1"] = to_pal1(page, T["wall_h"])
    tile("dado", ["22222222", "11111111", "11111111", "11111111",
                  "11111111", "11111111", "22222222", "11111111"])
    tile("pit", ["........"] * 8)
    tile("pit_rail", ["........", "........", "........", "........",
                      "........", "22222222", "33333333", "11111111"])
    tile("pit_third", ["........", "22222222", "11111111", "........",
                       "........", "........", "........", "........"])
    tile("pit_ties", ["........", "........", "........", "........",
                      "........", "........", "11111111", "........"])
    # Platform edge (palette 3): yellow tactile strip, then the lip.
    tile("edge", ["11111111", "22222222", "2.2.2.2.", "22222222",
                  ".2.2.2.2", "22222222", "2.2.2.2.", "22222222"])
    tile("lip", ["33333333", "11111111", "11111111", "11111111",
                 "11111111", "11111111", "11111111", "11111111"])
    # Floor: speckled concrete.
    tile("floor", ["11111111", "11111111", "11111211", "11111111",
                   "12111111", "11111111", "11111111", "11112111"])
    tile("floor2", ["11111111", "11121111", "11111111", "11111111",
                    "11111111", "11111112", "11111111", "21111111"])
    tile("floor_seam", ["11111111", "11111111", "11111111", "11111111",
                        "11111111", "11111111", "11111111", "22222222"])
    # Bench: wood slats on legs.
    tile("bench_top", ["........", "........", "........", "........",
                       "33333333", "22222222", "33333333", "22222222"])
    tile("bench_leg_l", ["11111111", ".2....2.", ".2....2.", ".2....2.",
                         ".2....2.", ".2....2.", "........", "........"])
    tile("bench_leg_r", ["11111111", ".2....2.", ".2....2.", ".2....2.",
                         ".2....2.", ".2....2.", "........", "........"])
    return T


def platform_screen(T):
    s = Screen(T["black"])
    # HUD (rows 0-4) is black; the game writes the text.
    s.palette(0, 0, 32, 2, 0)
    s.palette(0, 2, 32, 2, 1)
    s.palette(0, 4, 32, 2, 0)
    s.row(5, [T["beam"]] * 32)
    # Mosaic band, rows 6-7, palette 2, with a name tablet in the middle.
    s.palette(0, 6, 32, 2, 2)
    s.row(6, [T["mosaic_top"]] * 32)
    s.row(7, [T["mosaic_bot"]] * 32)
    s.row(8, [T["wall"]] * 32)
    for x0 in TABLET_XS:
        s.put(x0, 6, T["tabf_tl"])
        s.put(x0 + 9, 6, T["tabf_tr"])
        s.put(x0, 7, T["tabf_l"])
        s.put(x0 + 9, 7, T["tabf_r"])
        s.put(x0, 8, T["tabf_bl"])
        s.put(x0 + 9, 8, T["tabf_br"])
        for x in range(x0 + 1, x0 + 9):
            s.put(x, 6, T["tabf_t"])
            s.put(x, 7, T["tab_ "])
            s.put(x, 8, T["tabf_b"])
    s.row(9, [T["wall"]] * 32)
    s.palette(0, 10, 32, 2, 1)
    for y in (10, 11):
        s.row(y, [T["wall_h1"]] * 32)
    s.row(12, [T["wall_h"]] * 32)
    s.row(13, [T["dado"]] * 32)
    s.row(14, [T["pit"]] * 32)
    s.row(15, [T["pit_third"]] * 32)
    s.row(16, [T["pit_ties"]] * 32)
    s.row(17, [T["pit_rail"]] * 32)
    s.palette(0, 18, 32, 2, 3)
    s.row(18, [T["edge"]] * 32)
    s.row(19, [T["lip"]] * 32)
    for y in range(20, 30):
        s.row(y, [T["floor"] if (x + y) % 3 else T["floor2"] for x in range(32)])
    s.row(29, [T["floor_seam"]] * 32)
    # Benches.
    for bx in (9, 20):
        s.row(22, [T["bench_top"]] * 4, bx)
        s.row(23, [T["bench_leg_l"], T["floor"], T["floor"], T["bench_leg_r"]], bx)
    return s


def build_train(page):
    T = {}

    def tile(name, rows):
        T[name] = page.add(parse(rows), name)

    tile("black", ["........"] * 8)
    # Stainless car side (palette 0: black, dark gray, light gray, white).
    tile("roof", ["........", "........", "11111111", "22222222",
                  "33333333", "22222222", "22222222", "33333333"])
    tile("body", ["22222222", "33333333", "22222222", "22222222",
                  "33333333", "22222222", "22222222", "33333333"])
    tile("body_top", ["22222222", "22222222", "33333333", "22222222",
                      "22222222", "11111111", "11111111", "11111111"])
    tile("win", ["11111111", "1.......", "1.......", "1.......",
                 "1.......", "1.......", "1.......", "1......."])
    tile("win_r", ["11111111", ".......1", ".......1", ".......1",
                   ".......1", ".......1", ".......1", ".......1"])
    tile("win_m", ["11111111", "........", "........", "........",
                   "........", "........", "........", "........"])
    tile("win_p1", ["11111111", "........", "...22...", "..2222..",
                    "...22...", "..1221..", ".122221.", ".122221."])
    tile("win_p2", ["11111111", "........", "........", "....22..",
                    "...2222.", "....22..", "...1221.", "..122221"])
    tile("win_bot", ["1.......", "1.......", "1.......", "1.......",
                     "11111111", "22222222", "33333333", "22222222"])
    tile("win_bot_r", [".......1", ".......1", ".......1", ".......1",
                       "11111111", "22222222", "33333333", "22222222"])
    tile("win_bot_m", ["........", "........", "........", "........",
                       "11111111", "22222222", "33333333", "22222222"])
    tile("win_bot_p", [".122221.", ".122221.", ".122221.", ".122221.",
                       "11111111", "22222222", "33333333", "22222222"])
    tile("skirt", ["22222222", "33333333", "22222222", "11111111",
                   "1.1.1.1.", "........", "........", "........"])
    tile("truck", ["........", "..1111..", ".122221.", "12333321",
                   "12322321", ".122221.", "22111122", "33333333"])
    tile("truck_gap", ["........", "........", "........", "........",
                       "11111111", "........", "22222222", "33333333"])
    tile("end", ["..1..1..", "..1..1..", "..1..1..", "..1..1..",
                 "..1..1..", "..1..1..", "..1..1..", "..1..1.."])
    tile("end_roof", ["........", "........", "........", "..1..1..",
                      "..1..1..", "..1..1..", "..1..1..", "..1..1.."])
    tile("end_rail", ["........", "........", "........", "........",
                      "........", "22222222", "33333333", "11111111"])
    # Doors: two panels with tall windows; the seam is between panels.
    tile("door_l", ["21111113", "21.....3", "21.....3", "21.....3",
                    "21.....3", "21.....3", "21.....3", "21.....3"])
    tile("door_r", ["31111112", "3.....12", "3.....12", "3.....12",
                    "3.....12", "3.....12", "3.....12", "3.....12"])
    tile("door_lb", ["21.....3", "21.....3", "21111113", "22222223",
                     "22222223", "22222223", "22222223", "22222223"])
    tile("door_rb", ["3.....12", "3.....12", "31111112", "32222222",
                     "32222222", "32222222", "32222222", "32222222"])
    tile("door_lp", ["22222223", "22222223", "22222223", "22222223",
                     "22222223", "22222223", "22222223", "22222223"])
    tile("door_rp", ["32222222", "32222222", "32222222", "32222222",
                     "32222222", "32222222", "32222222", "32222222"])
    tile("door_l2", ["22222223", "22222223", "22222223", "22222223",
                     "22222223", "22222223", "22222223", "11111111"])
    tile("door_r2", ["32222222", "32222222", "32222222", "32222222",
                     "32222222", "32222222", "32222222", "11111111"])
    tile("door_top_l", ["22222222", "22222222", "33333333", "22222222",
                        "22222222", "21111111", "21111111", "21111113"])
    tile("door_top_r", ["22222222", "22222222", "33333333", "22222222",
                        "22222222", "11111112", "11111112", "31111112"])
    # Open doorway: lit interior with a grab pole.
    tile("open", ["22222222", "33333333", "...33...", "...33...",
                  "...33...", "...33...", "...33...", "...33..."])
    tile("open_m", ["........", "...33...", "...33...", "...33...",
                    "...33...", "...33...", "...33...", "...33..."])
    tile("open_floor", ["...33...", "...33...", "...33...", "11111111",
                        "22222222", "22222222", "33333333", "22222222"])
    # Door cells of row 11, which is in palette 1.
    for name in ("open", "door_top_l", "door_top_r"):
        T[name + "1"] = to_pal1(page, T[name])
    # LED sign (palette 1): black face, gray bezel, amber text.
    tile("led_l", ["11111111", "1.......", "1.......", "1.......",
                   "1.......", "1.......", "1.......", "11111111"])
    tile("led_r", ["11111111", ".......1", ".......1", ".......1",
                   ".......1", ".......1", ".......1", "11111111"])
    tile("led_m", ["11111111", "........", "........", "........",
                   "........", "........", "........", "11111111"])
    return T


DOOR_COLS = (3, 25)
TABLET_XS = (2, 20)
SIGN_X = 9
SIGN_W = 14


def train_screen(page, T, wall):
    """Nametable 1 of the platform: one car, wall and HUD rows blank."""
    s = Screen(wall.tiles[0][0])
    for y in range(30):
        s.tiles[y] = list(wall.tiles[y])
    s.pal = [list(r) for r in wall.pal]
    car_rows = {
        10: "roof", 11: "body_top", 12: "win", 13: "win_bot",
        14: "body", 15: "body", 16: "skirt", 17: "truck_gap",
    }
    for y, name in car_rows.items():
        s.row(y, [T[name]] * 32)
    for x in range(1, 31):
        s.put(x, 12, T["win_m"])
        s.put(x, 13, T["win_bot_m"])
    # People in the windows.
    for x in (2, 10, 12, 19, 21, 29):
        s.put(x, 12, T["win_p1"] if x % 2 else T["win_p2"])
        s.put(x, 13, T["win_bot_p"])
    for x in (8, 13, 18, 23, 28):
        s.put(x, 12, T["win"])
        s.put(x, 13, T["win_bot"])
    for x in (3, 13, 23, 30):
        s.put(x, 12, T["win_r"])
        s.put(x, 13, T["win_bot_r"])
    for d in DOOR_COLS:
        s.row(11, [T["door_top_l"], T["door_l"], T["door_r"], T["door_top_r"]], d)
        for y, (l, r) in {12: ("door_l", "door_r"), 13: ("door_lb", "door_rb"),
                          14: ("door_lp", "door_rp"), 15: ("door_lp", "door_rp"),
                          16: ("door_l2", "door_r2")}.items():
            s.row(y, [T["body"], T[l], T[r], T["body"]], d)
            s.put(d, y, T["body"])
            s.put(d + 3, y, T["body"])
        s.put(d, 11, T["body_top"])
        s.put(d + 3, 11, T["body_top"])
        s.row(11, [T["door_top_l"], T["door_top_r"]], d + 1)
        s.row(12, [T["door_l"], T["door_r"]], d + 1)
    for y in range(10, 18):
        s.put(0, y, T["end_roof"] if y == 10 else T["end"])
        s.put(31, y, T["end_roof"] if y == 10 else T["end"])
    s.put(0, 17, T["end_rail"])
    s.put(31, 17, T["end_rail"])
    for x in (3, 4, 9, 10, 21, 22, 27, 28):
        s.put(x, 17, T["truck"])
    # LED sign above the windows between the doors.
    for y in (10, 11):
        s.row(y, [to_pal1(page, t) for t in s.tiles[y]])
    s.palette(0, 10, 32, 2, 1)
    s.put(SIGN_X - 1, 11, T["led_l"])
    s.put(SIGN_X + SIGN_W, 11, T["led_r"])
    for x in range(SIGN_X, SIGN_X + SIGN_W):
        s.put(x, 11, T["led_m"])
    for x in range(SIGN_X - 1, SIGN_X + SIGN_W + 1):
        s.put(x, 10, T["black"])
    s.palette(0, 12, 32, 6, 0)
    return s


# --------------------------------------------------------------------
# Car interior (CHR page 2)
# --------------------------------------------------------------------
#
# The far wall of the car, seen from the aisle. Rows 9-13 are the
# window band: a 64-column ring across both nametables that scrolls
# past the scenery, like the platform's track band. Window posts and
# door frames in those rows are sprites, eight per scanline.
#
# Palettes: 0 floor (black, dark gray, light gray, white), 1 LED sign
# (amber), 2 window band (black, station mosaic, dark gray, cream),
# 3 seats and sky (black, blue, dark gray, cream). Rows 8-15 take
# palette 2 or 3 per 16 columns from the scenery, so every interior
# tile in those rows uses only colors 0, 2, and 3.

IN_BAND_ROW = 9
IN_BAND_ROWS = 5
IN_DOORS = (2, 24)
IN_POSTS = (128,)
IN_LED_X = 2
IN_LED_W = 28

# Fixed text for the car's LED sign and HUD, as font codes.
MESSAGES = [
    ("NEXT", "The next stop is"),
    ("THIS", "This is"),
    ("LAST", "This is the last stop"),
    ("LEAVE", "Please leave the train"),
    ("CLEAR1", "Stand clear of the"),
    ("CLEAR2", "closing doors, please"),
    ("XFER", "Transfer is available"),
    ("GOING", "This train goes to"),
    ("TO", "to "),
    ("HUD_NEXT", "Next: "),
    ("HUD_AT", "At: "),
    ("STOPS", "Next stops"),
    ("TRAINS", "Trains here"),
]


def build_interior(page):
    T = {}

    def tile(name, rows):
        T[name] = page.add(parse(rows), name)

    tile("black", ["........"] * 8)
    # Station tablet letters, dark on cream; one run of tiles.
    page.align_run(len(CHARSET))
    for ch in CHARSET:
        px = solid(3)
        for y, row in enumerate(GLYPHS[ch]):
            for x, c in enumerate(row):
                if c == "#":
                    px[y][x + 1] = 0
        T["tab_" + ch] = page.add(px, None, dedup=False)
    # Ceiling (palette 3): cream panels with a light fixture.
    tile("ceil", ["22222222", "33333333", "33333333", "33333333",
                  "33333333", "33333333", "22222222", "........"])
    tile("ceil_lamp", ["22222222", "33333333", "2......2", "23333332",
                       "23333332", "2......2", "22222222", "........"])
    # Advertising cards (palette 3) between the doors.
    tile("ad_l", ["22222222", "21111111", "21313131", "21111111",
                  "21333331", "21111111", "22222222", "........"])
    tile("ad_m", ["22222222", "11111111", "13131313", "11111111",
                  "33333111", "11111111", "22222222", "........"])
    tile("ad_r", ["22222222", "11111112", "13131312", "11111112",
                  "13311112", "11111112", "22222222", "........"])
    tile("wall_up", ["33333333", "33333333", "33333333", "22222222",
                     "33333333", "33333333", "33333333", "22222222"])
    # Window frame above and below the band (colors 0, 2, 3 only).
    tile("win_top", ["33333333", "33333333", "33333333", "22222222",
                     "22222222", "33333333", "22222222", "........"])
    tile("sill", ["........", "22222222", "33333333", "33333333",
                  "22222222", "33333333", "33333333", "22222222"])
    tile("wall_lo", ["33333333", "33333333", "33333333", "22222222",
                     "33333333", "33333333", "33333333", "22222222"])
    # Bench seats (palette 3), two cells per seat.
    tile("seat_back_l", ["22222222", "21111111", "21111111", "21111111",
                         "21111111", "21111111", "21111111", "21111111"])
    tile("seat_back_r", ["22222222", "11111112", "11111112", "11111112",
                         "11111112", "11111112", "11111112", "11111112"])
    tile("seat_l", ["23333333", "21111111", "21111111", "21111111",
                    "21111111", "22222222", "........", "........"])
    tile("seat_r", ["33333332", "11111112", "11111112", "11111112",
                    "11111112", "22222222", "........", "........"])
    tile("seat_base", ["........", "..2..2..", "........", "22222222",
                       "2.2.2.2.", "22222222", "........", "........"])
    tile("skirt", ["22222222", "........", "........", "........",
                   "........", "........", "........", "........"])
    # Floor (palette 0): speckled tread.
    tile("floor", ["11111111", "11111111", "11121111", "11111111",
                   "11111111", "11111112", "11111111", "11111111"])
    tile("floor2", ["11111111", "12111111", "11111111", "11111111",
                    "11112111", "11111111", "11111111", "11111111"])
    tile("floor_edge", ["22222222", "11111111", "11111111", "11111111",
                        "11111111", "11111111", "11111111", "11111111"])
    # Doors: a header, then two stainless leaves below the glass.
    tile("door_head", ["22222222", "22222222", "33333333", "33333333",
                       "22222222", "33333333", "22222222", "........"])
    tile("door_frame_l", ["..233333", "..233333", "..233333", "..233333",
                          "..233333", "..233333", "..233333", "..233333"])
    tile("door_frame_r", ["333332..", "333332..", "333332..", "333332..",
                          "333332..", "333332..", "333332..", "333332.."])
    tile("leaf", ["33333333", "33333333", "22222222", "33333333",
                  "33333333", "33333333", "33333333", "33333333"])
    tile("leaf_seam_l", ["3333332.", "3333332.", "2222222.", "3333332.",
                         "3333332.", "3333332.", "3333332.", "3333332."])
    tile("leaf_seam_r", [".2333333", ".2333333", ".2222222", ".2333333",
                         ".2333333", ".2333333", ".2333333", ".2333333"])
    tile("leaf_kick", ["33333333", "33333333", "33333333", "22222222",
                       "22222222", "22222222", "22222222", "........"])
    tile("leaf_kick_l", ["3333332.", "3333332.", "3333332.", "2222222.",
                         "2222222.", "2222222.", "2222222.", "........"])
    tile("leaf_kick_r", [".2333333", ".2333333", ".2333333", ".2222222",
                         ".2222222", ".2222222", ".2222222", "........"])
    tile("threshold", ["22222222", "33333333", "22222222", "11111111",
                       "11111111", "11111111", "11111111", "11111111"])
    # Open doorway: the platform beyond (colors 0, 2, 3).
    tile("out_edge", ["33333333", "3.3.3.3.", "33333333", ".3.3.3.3",
                      "33333333", "22222222", "22222222", "22222222"])
    tile("out_floor", ["22222222", "22222222", "22232222", "22222222",
                       "22222222", "22222223", "22222222", "22222222"])
    tile("out_floor_lo", ["22222222", "22222222", "22232222", "22222222",
                          "22222222", "22222222", "22222222", "11111111"])
    # LED sign (palette 1), as on the car sides.
    tile("led_l", ["11111111", "1.......", "1.......", "1.......",
                   "1.......", "1.......", "1.......", "11111111"])
    tile("led_r", ["11111111", ".......1", ".......1", ".......1",
                   ".......1", ".......1", ".......1", "11111111"])

    # Scenery in the window band (palette 2 or 3).
    tile("tn_dark", ["........", "........", "........", "...2....",
                     "........", "........", "........", "........"])
    tile("tn_cable", ["........", "22222222", "........", "22222222",
                      "........", "........", "........", "........"])
    tile("tn_beam", ["..2332..", "..2332..", "..2332..", "..2332..",
                     "..2332..", "..2332..", "..2332..", "..2332.."])
    tile("tn_beam_top", ["22222222", "..2332..", "..2332..", "..2332..",
                         "..2332..", "..2332..", "..2332..", "..2332.."])
    tile("tn_lamp", ["...22...", "..2332..", ".233332.", ".233332.",
                     "..2332..", "...22...", "........", "........"])
    tile("tn_bench", ["........", "........", "........", "........",
                      "22222222", "2.2.2.2.", "........", "........"])
    tile("mos_t", ["33333333", "31313131", "13131313", "22222222",
                   "21212121", "12121212", "21212121", "12121212"])
    tile("mos_b", ["21212121", "12121212", "21212121", "12121212",
                   "22222222", "13131313", "31313131", "33333333"])
    tile("st_wall", ["33333332", "33333332", "33333332", "33333332",
                     "33333332", "33333332", "33333332", "22222222"])
    tile("st_edge", ["33333333", "33333333", "22222222", "3.3.3.3.",
                     "22222222", "........", "........", "........"])
    tile("st_col", ["..2222..", "..2332..", "..2332..", "..2332..",
                    "..2332..", "..2332..", "..2332..", "..2222.."])
    tile("st_col_edge", ["..2222..", "..2332..", "22222222", "3.3.3.3.",
                         "22222222", "........", "........", "........"])
    tile("st_head", ["...22...", "..2222..", "..2222..", "...22...",
                     "..2222..", ".222222.", ".222222.", ".222222."])
    tile("st_body", [".222222.", ".222222.", ".222222.", "..2..2..",
                     "..2..2..", "22222222", "3.3.3.3.", "22222222"])
    tile("tabf_tl", ["33333333", "31313131", "13131313", "22222222",
                     "21211111", "12213333", "21213333", "12213333"])
    tile("tabf_t", ["33333333", "31313131", "13131313", "22222222",
                    "11111111", "33333333", "33333333", "33333333"])
    tile("tabf_tr", ["33333333", "31313131", "13131313", "22222222",
                     "11111212", "33331221", "33331212", "33331221"])
    tile("tabf_l", ["21213333", "12213333", "21213333", "12213333",
                    "21213333", "12213333", "21213333", "12213333"])
    tile("tabf_r", ["33331212", "33331221", "33331212", "33331221",
                    "33331212", "33331221", "33331212", "33331221"])
    tile("tabf_bl", ["21213333", "12211111", "21212222", "12121212",
                     "22222222", "13131313", "31313131", "33333333"])
    tile("tabf_b", ["33333333", "11111111", "22222222", "12121212",
                    "22222222", "13131313", "31313131", "33333333"])
    tile("tabf_br", ["33331212", "11111221", "22221212", "12121212",
                     "22222222", "13131313", "31313131", "33333333"])
    # Elevated: sky, rooftops, and the el structure.
    tile("sky", ["11111111"] * 8)
    tile("bld", ["22222222", "23322332", "22222222", "22222222",
                 "23322332", "22222222", "22222222", "22222222"])
    tile("bld_top", ["11111111", "11111111", "11111111", "22222222",
                     "22222222", "23322332", "22222222", "22222222"])
    tile("bld_top2", ["11111111", "11122111", "11122111", "22222222",
                      "22222222", "22222222", "23322332", "22222222"])
    tile("el_girder", ["22222222", "2.2..2.2", "2..22..2", "2..22..2",
                       "2.2..2.2", "22222222", "........", "........"])
    tile("canopy", ["22222222", "22222222", "33333333", "........",
                    "........", "........", "........", "........"])
    tile("canopy_post", ["22222222", "22222222", "33333333", "...22...",
                         "...22...", "...22...", "...22...", "...22..."])
    tile("op_post", ["...22...", "...22...", "...22...", "...22...",
                     "...22...", "...22...", "...22...", "...22..."])
    tile("op_edge", ["...22...", "...22...", "22222222", "33333333",
                     "3.3.3.3.", "22222222", "........", "........"])
    tile("op_edge_m", ["11111111", "11111111", "22222222", "33333333",
                       "3.3.3.3.", "22222222", "........", "........"])
    tile("sign_l", ["........", ".3333333", ".3......", ".3......",
                    ".3......", ".3......", ".3......", ".3333333"])
    tile("sign_r", ["........", "3333333.", "......3.", "......3.",
                    "......3.", "......3.", "......3.", "3333333."])
    return T


def _jolt_tiles():
    # A rail-joint jolt scrolls the car down a line, so the last scanline
    # shows nametable row 30: the attribute bytes, read as tile numbers.
    # Keep every tile those bytes can name blank. The band quadrants use
    # palette 2 or 3; the top attribute rows are fixed.
    out = {0x00, 0xF5}
    for v in range(256):
        if all((v >> (2 * q)) & 3 in (2, 3) for q in range(4)):
            out.add(v)
    return out


JOLT_TILES = _jolt_tiles()


def interior_screen(T):
    s = Screen(T["black"])
    s.palette(0, 0, 32, 4, 0)
    s.palette(0, 4, 32, 2, 1)
    s.palette(0, 6, 32, 2, 3)
    s.palette(0, 8, 32, 8, 2)
    s.palette(0, 16, 32, 4, 3)
    s.palette(0, 20, 32, 10, 0)
    s.put(IN_LED_X - 1, 5, T["led_l"])
    s.put(IN_LED_X + IN_LED_W, 5, T["led_r"])
    s.row(6, [T["ceil_lamp"] if x % 8 in (2, 3, 4) else T["ceil"] for x in range(32)])
    s.row(7, [T["wall_up"]] * 32)
    s.row(7, [T["ad_l"]] + [T["ad_m"]] * 4 + [T["ad_r"]], 9)
    s.row(7, [T["ad_l"]] + [T["ad_m"]] * 3 + [T["ad_r"]], 17)
    s.row(8, [T["win_top"]] * 32)
    s.row(14, [T["sill"]] * 32)
    s.row(15, [T["wall_lo"]] * 32)
    for x in range(32):
        left = x % 2 == 0
        s.put(x, 16, T["seat_back_l" if left else "seat_back_r"])
        s.put(x, 17, T["seat_l" if left else "seat_r"])
        s.put(x, 18, T["seat_base"])
    s.row(19, [T["skirt"]] * 32)
    for y in range(20, 30):
        s.row(y, [T["floor"] if (x * 3 + y) % 5 else T["floor2"] for x in range(32)])
    s.row(20, [T["floor_edge"]] * 32)
    for d in IN_DOORS:
        s.row(7, [T["door_head"]] * 6, d)
        for y in range(14, 19):
            s.put(d, y, T["door_frame_l"])
            s.put(d + 5, y, T["door_frame_r"])
            leaf = "leaf_kick" if y == 18 else "leaf"
            s.row(y, [T[leaf], T[leaf + "_seam_l" if y < 18 else "leaf_kick_l"],
                      T[leaf + "_seam_r" if y < 18 else "leaf_kick_r"], T[leaf]], d + 1)
        s.put(d, 19, T["door_frame_l"])
        s.put(d + 5, 19, T["door_frame_r"])
        s.row(19, [T["threshold"]] * 4, d + 1)
    return s


# --------------------------------------------------------------------
# Sprites (CHR page 1)
# --------------------------------------------------------------------

# 16x32, facing left (the direction draw_player leaves unflipped;
# it mirrors this for a rightward-facing player). Traced from
# River City Ransom's Alex's 3/4 idle.
# Rows 0-23 use sprite palette 0: 1 black hair and outline, 2 skin,
# 3 white shirt. The legs below are Alex's own, from the same
# sheet: 1 is the black outline and shoes, B is the blue denim.
# Denim is drawn as a second pair of tiles on sprite palette 2.
BODY = [
    "11111111111.....",
    "111111112111....",
    "111111122211....",
    "111111222211....",
    "111122211211....",
    ".12222133211....",
    ".31221333211....",
    ".31221333212....",
    ".22222222222....",
    ".222222222111...",
    "1222222222213331",
    "1211112213333331",
    "3122222213333331",
    "3311111113333331",
    "1111113111111333",
    "222133112222111.",
    "2222131222221221",
    "2222131222221221",
    "2222133122222121",
    "2221333122222221",
    "1113333111111221",
    "113333331222221.",
    ".11111111111111.",
    ".1111111111111..",
]
# Alex's legs from the RCR sheet, mirrored with the torso.
# 1 is black outline and shoes. B is blue denim.
STAND_LEGS = [
    "..1BB11BBBB1BB1.",
    "..1BBB1BBBBB111.",
    "..1BBBB1BBBBBB1.",
    "..1BBBB1BBBBBB1.",
    "...1BBB1BBBBBBB1",
    "...1BBB1BBBBBBB1",
    "...11BB1111BBBB1",
    "..11111111111111",
]
STRIDE_LEGS = [
    [
        ".11111BBBB1BB1..",
        ".1BB1BBBBBB111..",
        ".1B1BBBBBBBBB1..",
        "..11B11BBBBB1...",
        "..11BBBBBBB1....",
        "...1BBBBBBB1....",
        "...1111BBBB1....",
        "..1111111111....",
    ],
    [
        ".1B11BBBBBB1B1..",
        "1BBB1BBBBBBB11..",
        "1BBB1BBBBBBBB1..",
        "BBBBB1BBBBBBBB1.",
        "BBBBB1BB11BBBB1.",
        "BBBBBB1BBBBBB11.",
        "11BBBB1111BB11..",
        "111111.111111...",
    ],
]


def legs_for(phase):
    """Phase 0 stands. Phases 1 and 2 are the two RCR strides."""
    if phase == 0:
        return STAND_LEGS
    return STRIDE_LEGS[phase - 1]


def leg_black(rows):
    """Outline and shoes. Denim is left transparent."""
    return ["".join("1" if c == "1" else "." for c in r) for r in rows]


def leg_blue(rows):
    """Denim only, as color 1 of sprite palette 2."""
    return ["".join("1" if c == "B" else "." for c in r) for r in rows]


PLAYER = BODY + leg_black(STAND_LEGS)


def walk_frame(base, phase):
    """Keep the head and torso. Swap in one RCR leg pose."""
    rows = list(base)
    rows[24:32] = leg_black(legs_for(phase))
    return rows


def split_16(rows):
    """Cut a 16-wide picture into 8x8 tiles, column-major per 8 rows."""
    tiles = []
    for ty in range(len(rows) // 8):
        for tx in range(len(rows[0]) // 8):
            px = []
            for y in range(8):
                r = rows[ty * 8 + y][tx * 8: tx * 8 + 8]
                px.append([0 if c == "." else int(c) for c in r])
            tiles.append(px)
    return tiles


def build_sprites(page):
    T = {}
    for f in range(3):
        for i, px in enumerate(split_16(walk_frame(PLAYER, f))):
            T[f"player{f}_{i}"] = page.add(px, f"player{f}_{i}", dedup=False)
        # Denim sits on top of the outline tiles, same 16x8 footprint.
        for i, px in enumerate(split_16(leg_blue(legs_for(f)))):
            T[f"jeans{f}_{i}"] = page.add(px, f"jeans{f}_{i}", dedup=False)
    circle = ["..####..", ".######.", "########", "########",
              "########", "########", ".######.", "..####.."]
    for k in (1, 2):
        for g, rows in BULLET_GLYPHS.items():
            for dark in (False, True):
                px = [[k if c == "#" else 0 for c in r] for r in circle]
                for y, r in enumerate(rows):
                    for x, c in enumerate(r):
                        if c == "#":
                            px[y + 1][x + 2] = 0 if dark else 3
                T[f"bullet{k}_{g}_{int(dark)}"] = page.add(px, f"bullet{k}_{g}_{int(dark)}")
    # Interior window posts: 8 wide, light gray steel with a highlight.
    # Palette 0 is black, skin, white for Alex. Steel uses black
    # and white, not the skin color.
    post = ["..1331..", "..1331..", "..1331..", "..1331..",
            "..1331..", "..1331..", "..1331..", "..1331.."]
    T["post"] = page.add([[int(c) if c != "." else 0 for c in r] for r in post], "post")
    seam_l = ["...13331", "...13331", "...13331", "...13331",
              "...13331", "...13331", "...13331", "...13331"]
    T["seam_l"] = page.add([[int(c) if c != "." else 0 for c in r] for r in seam_l], "seam_l")
    seam_r = ["13331...", "13331...", "13331...", "13331...",
              "13331...", "13331...", "13331...", "13331..."]
    T["seam_r"] = page.add([[int(c) if c != "." else 0 for c in r] for r in seam_r], "seam_r")
    # Car interior, over the window band. Palette 0 is black / skin /
    # white, so the frames are black and white rather than skin.
    for name, rows in {
        "dedge_l": ["1333331."] * 8,
        "dedge_r": [".1333331"] * 8,
        "dcenter": ["33311333"] * 8,
        "wpost": [".133331."] * 8,
    }.items():
        T[name] = page.add([[int(c) if c != "." else 0 for c in r] for r in rows], name)
    # Pause map markers, centered on pixel (3, 3): a stop in its
    # route's color k with a white center, and the player.
    for k in (1, 2):
        rows = ["........", "..kkk...", ".k333k..", ".k333k..",
                ".k333k..", "..kkk...", "........", "........"]
        T[f"dot{k}"] = page.add([[k if c == "k" else int(c) if c != "." else 0
                                  for c in r] for r in rows], f"dot{k}")
    here = ["..333...", ".32223..", "3222223.", "3222223.",
            "3222223.", ".32223..", "..333...", "........"]
    T["here"] = page.add([[int(c) if c != "." else 0 for c in r] for r in here], "here")
    return T


# --------------------------------------------------------------------
# Pause map (CHR page 3)
# --------------------------------------------------------------------

# The map covers columns 0-17; the side panel starts at MAP_PANEL_X.
MAP_COLS = 18
MAP_PANEL_X = 18
# Line color of each route color group on the map, for the background
# palettes that light up the routes the player can ride.
GROUP_MAP_COLOR = {
    "red": 0x16, "green": 0x1A, "purple": 0x14, "blue": 0x12,
    "orange": 0x27, "lime": 0x2A, "brown": 0x17, "gray": 0x30,
    "yellow": 0x28, "shuttle": 0x30,
}
# Borough names on the map: (text, column, row). Manhattan has no
# room beside it that isn't another borough.
MAP_LABELS = (("Bronx", 13, 1), ("Queens", 12, 14), ("Brooklyn", 3, 28))


def read_ne_table(path, name):
    with open(path, encoding="utf-8") as f:
        src = f.read()
    start = src.index(f"const {name}:")
    body = src[src.index("[", src.index("=", start)) + 1:src.index("]", src.index("=", start))]
    return [int(v) for v in body.replace("\n", " ").split(",") if v.strip()]


def map_bitmap(data_dir):
    """Every route as one-pixel lines between its stops."""
    st_path = os.path.join(data_dir, "data_stations.ne")
    ln_path = os.path.join(data_dir, "data_lines.ne")
    xs = read_ne_table(st_path, "ST_MAP_X")
    ys = read_ne_table(st_path, "ST_MAP_Y")
    st_lo = read_ne_table(ln_path, "PS_ST_LO")
    st_hi = read_ne_table(ln_path, "PS_ST_HI")
    off_lo = read_ne_table(ln_path, "PAT_OFF_LO")
    off_hi = read_ne_table(ln_path, "PAT_OFF_HI")
    lens = read_ne_table(ln_path, "PAT_LEN")
    img = [[0] * (MAP_COLS * 8) for _ in range(240)]

    def line(x0, y0, x1, y1):
        dx, dy = abs(x1 - x0), -abs(y1 - y0)
        sx = 1 if x0 < x1 else -1
        sy = 1 if y0 < y1 else -1
        err = dx + dy
        while True:
            img[y0][x0] = 1
            if x0 == x1 and y0 == y1:
                return
            e2 = 2 * err
            if e2 >= dy:
                err += dy
                x0 += sx
            if e2 <= dx:
                err += dx
                y0 += sy

    for p, n in enumerate(lens):
        off = off_hi[p] * 256 + off_lo[p]
        stops = [st_hi[off + k] * 256 + st_lo[off + k] for k in range(n)]
        for a, b in zip(stops, stops[1:]):
            line(xs[a], ys[a], xs[b], ys[b])
    return img


def merge_tiles(cells, budget):
    """Replace the rarest tiles with their nearest look-alikes until at
    most `budget` distinct tiles remain."""
    counts = {}
    for row in cells:
        for t in row:
            counts[t] = counts.get(t, 0) + 1
    blank = tuple(tuple([0] * 8) for _ in range(8))

    def dist(a, b):
        return sum(pa != pb for ra, rb in zip(a, b) for pa, pb in zip(ra, rb))

    remap = {}
    while len(counts) > budget:
        best = None
        for a in counts:
            if a == blank:
                continue
            for b in counts:
                if a == b or counts[b] < counts[a]:
                    continue
                d = dist(a, b) * counts[a]
                if best is None or d < best[0]:
                    best = (d, a, b)
        _, a, b = best
        counts[b] += counts.pop(a)
        remap[a] = b
        for k, v in remap.items():
            if v == a:
                remap[k] = b
    return [[remap.get(t, t) for t in row] for row in cells]


def build_map(page, data_dir):
    img = map_bitmap(data_dir)
    T = {}
    T["rule"] = page.add(parse(["...1...."] * 8), "rule")
    cells = [[tuple(tuple(img[ty * 8 + y][tx * 8:tx * 8 + 8]) for y in range(8))
              for tx in range(MAP_COLS)] for ty in range(30)]
    labels = set()
    for text, x0, y in MAP_LABELS:
        for i in range(len(text)):
            labels.add((x0 + i, y))
    blank = tuple(tuple([0] * 8) for _ in range(8))
    for (x, y) in labels:
        assert cells[y][x] == blank, f"map label covers a line at {x}, {y}"
    cells = merge_tiles(cells, 256 - len(page.tiles) + 1)
    s = Screen(0)
    for ty in range(30):
        for tx in range(MAP_COLS):
            if cells[ty][tx] != blank:
                s.put(tx, ty, page.add([list(r) for r in cells[ty][tx]], None))
    for text, x0, y in MAP_LABELS:
        s.text(x0, y, text)
    for y in range(1, 29):
        s.put(MAP_PANEL_X, y, T["rule"])
    s.palette(MAP_PANEL_X, 0, 32 - MAP_PANEL_X, 30, 3)
    return T, s


def emit_page(name, page_no, page, start=None):
    data = []
    for px in page.tiles[page.first if start is None else start:]:
        data.extend(chr_bytes(px))
    lines = []
    for i in range(0, len(data), 16):
        lines.append("        " + ", ".join(f"0x{b:02X}" for b in data[i:i + 16]))
    return (f"sprite {name} {{\n    table: {page_no}\n    chr: [\n"
            + ",\n".join(lines) + "\n    ]\n}\n")


def table(name, values):
    rows = []
    for i in range(0, len(values), 32):
        rows.append("    " + ", ".join(str(v) for v in values[i:i + 32]))
    return f"const {name}: u8[{len(values)}] = [\n" + ",\n".join(rows) + "\n]\n"


def main():
    out_dir = sys.argv[1]
    plat = Page("platform", 1)
    PT = build_platform(plat)
    TT = build_train(plat)
    wall = platform_screen(PT)
    train = train_screen(plat, TT, wall)

    spr = Page("sprites", 0, font=False)
    ST = build_sprites(spr)

    inner = Page("interior", 1, reserved=JOLT_TILES)
    IT = build_interior(inner)
    car = interior_screen(IT)

    mpage = Page("map", 1)
    MT, map_scr = build_map(mpage, out_dir)

    chr_out = ["// Generated by examples/subway/tools/gen_gfx.py. Do not edit by hand.", ""]
    chr_out.append(emit_page("PlatformTiles", 0, plat))
    chr_out.append(emit_page("SpriteTiles", 1, spr))
    chr_out.append(emit_page("InteriorTiles", 2, inner, start=0))
    chr_out.append(emit_page("MapTiles", 3, mpage, start=0))
    with open(os.path.join(out_dir, "gfx_chr.ne"), "w") as f:
        f.write("\n".join(chr_out))

    scr = ["// Generated by examples/subway/tools/gen_gfx.py. Do not edit by hand.", ""]
    scr.append(table("NT_PLATFORM", wall.bytes()))
    scr.append(table("NT_TRAIN", train.bytes()))
    scr.append(table("NT_INTERIOR", car.bytes()))
    with open(os.path.join(out_dir, "gfx_screens.ne"), "w") as f:
        f.write("\n".join(scr))
    with open(os.path.join(out_dir, "gfx_map.ne"), "w") as f:
        f.write("// Generated by examples/subway/tools/gen_gfx.py. Do not edit by hand.\n\n")
        f.write(table("NT_MAP", map_scr.bytes()))

    consts = ["// Generated by examples/subway/tools/gen_gfx.py. Do not edit by hand.", ""]
    for name, idx in sorted(TT.items()):
        if name.startswith(("door", "open")):
            consts.append(f"const T_{name.upper()}: u8 = {idx}")
    consts.append(f"const T_BLACK: u8 = {PT['black']}")
    consts.append(f"const T_TABLET: u8 = {PT['tab_ ']}")
    consts.append(f"const TABLET_FONT: u8 = {PT['tab_ ']}")
    for d, x in enumerate(DOOR_COLS):
        consts.append(f"const DOOR{d}_COL: u8 = {x}")
    consts.append(f"const SIGN_X: u8 = {SIGN_X}")
    consts.append(f"const SIGN_W: u8 = {SIGN_W}")
    for name, idx in sorted(ST.items()):
        if name.startswith("player") and name.endswith("_0"):
            consts.append(f"const S_{name[:-2].upper()}: u8 = {idx}")
    for f in range(3):
        consts.append(f"const S_JEANS{f}: u8 = {ST[f'jeans{f}_0']}")
        assert ST[f"jeans{f}_1"] == ST[f"jeans{f}_0"] + 1
    consts.append(f"const S_BULLET1: u8 = {ST['bullet1_1_0']}")
    consts.append(f"const S_BULLET2: u8 = {ST['bullet2_1_0']}")
    for g in BULLET_GLYPHS:
        for dark in (0, 1):
            assert (ST[f"bullet2_{g}_{dark}"] - ST[f"bullet1_{g}_{dark}"]
                    == ST["bullet2_1_0"] - ST["bullet1_1_0"])
    pal, tile, sp3 = [], [], []
    for _, glyph, group in ROUTES:
        p, k, color, dark = GROUP_STYLE[group]
        pal.append(p)
        tile.append(ST[f"bullet{k}_{glyph}_{int(dark)}"])
        sp3.append(color)
    consts.append("// Per route: sprite palette, bullet tile, and the color the")
    consts.append("// route needs in sprite palette 3 (0 for none).")
    consts.append(table("ROUTE_PAL", pal).rstrip())
    consts.append(table("ROUTE_TILE", tile).rstrip())
    consts.append(table("ROUTE_SP3", sp3).rstrip())
    consts.append("// Per route: its line color on the pause map, and the map dot")
    consts.append("// sprite in its bullet color.")
    consts.append(table("ROUTE_MAP", [GROUP_MAP_COLOR[g] for _, _, g in ROUTES]).rstrip())
    consts.append(table("ROUTE_DOT", [ST[f"dot{GROUP_STYLE[g][1]}"] for _, _, g in ROUTES]).rstrip())
    consts.append(f"const S_HERE: u8 = {ST['here']}")
    consts.append(f"const S_DOT2: u8 = {ST['dot2']}")
    consts.append(f"const MAP_PANEL_X: u8 = {MAP_PANEL_X}")
    consts.append(f"const FONT_BASE: u8 = {FONT_BASE}")
    consts.append(f"const S_POST: u8 = {ST['post']}")
    consts.append(f"const S_SEAM_L: u8 = {ST['seam_l']}")
    consts.append(f"const S_SEAM_R: u8 = {ST['seam_r']}")
    blob, offs, lens = [], [], []
    for i, (name, text) in enumerate(MESSAGES):
        consts.append(f"const MSG_{name}: u8 = {i}")
        offs.append(len(blob))
        lens.append(len(text))
        blob.extend(CHARSET.index(c) for c in text)
    assert len(blob) < 256
    consts.append(table("MSG_OFF", offs).rstrip())
    consts.append(table("MSG_LEN", lens).rstrip())
    consts.append(table("MSG_TEXT", blob).rstrip())
    for name in ("dedge_l", "dedge_r", "dcenter", "wpost"):
        consts.append(f"const S_{name.upper()}: u8 = {ST[name]}")
    consts.append("// Car interior page.")
    for name, idx in sorted(IT.items()):
        if not name.startswith("tab_"):
            consts.append(f"const I_{name.upper()}: u8 = {idx}")
    consts.append(f"const I_TAB_FONT: u8 = {IT['tab_ ']}")
    consts.append(f"const IN_BAND_ROW: u8 = {IN_BAND_ROW}")
    consts.append(f"const IN_BAND_ROWS: u8 = {IN_BAND_ROWS}")
    for d, x in enumerate(IN_DOORS):
        consts.append(f"const IN_DOOR{d}_COL: u8 = {x}")
    for d, x in enumerate(IN_POSTS):
        consts.append(f"const IN_POST{d}_X: u8 = {x}")
    consts.append(f"const IN_LED_X: u8 = {IN_LED_X}")
    consts.append(f"const IN_LED_W: u8 = {IN_LED_W}")
    with open(os.path.join(out_dir, "gfx_consts.ne"), "w") as f:
        f.write("\n".join(consts) + "\n")
    print(f"platform page: {len(plat.tiles)} tiles, sprites: {len(spr.tiles)} tiles, "
          f"interior: {len(inner.tiles)} tiles, map: {len(mpage.tiles)} tiles",
          file=sys.stderr)


if __name__ == "__main__":
    main()
