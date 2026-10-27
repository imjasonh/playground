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
# the player's outline color in palette 0.
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


def glyph_tile(ch, color=3):
    px = solid(0)
    for y, row in enumerate(GLYPHS[ch]):
        for x, c in enumerate(row):
            if c == "#":
                px[y][x + 1] = color
    return px


class Page:
    """A 256-tile CHR page with dedup by pixel content."""

    def __init__(self, name, first, font=True):
        self.name = name
        self.first = first
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
            idx = len(self.tiles)
            self.tiles.append(px)
            self.index.setdefault(key, idx)
        if name:
            self.names[name] = idx
        assert len(self.tiles) <= 256, f"page {self.name} is full"
        return idx

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
    # Stairway down at the right end of the platform.
    tile("stair", ["22222222", "33333333", "11111111", "11111111",
                   "22222222", "33333333", "11111111", "11111111"])
    tile("stair_rail_l", ["3.......", "3.......", "3.......", "3.......",
                          "3.......", "3.......", "3.......", "3......."])
    tile("rail_top", ["33333333", "........", "........", "........",
                      "........", "........", "........", "........"])
    # Passage arch at the left end.
    tile("arch", ["........", "........", "........", "........",
                  "........", "........", "........", "........"])
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
    for y in (10, 11, 12):
        s.row(y, [T["wall_h"]] * 32)
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
    # Stairs down at the right.
    for y in range(21, 29):
        s.row(y, [T["stair"]] * 3, 28)
        s.put(27, y, T["stair_rail_l"])
    s.row(20, [T["rail_top"]] * 5, 27)
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
    # LED sign (palette 1): black face with an amber frame.
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


def train_screen(T, wall):
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
    s.palette(SIGN_X - 1, 10, SIGN_W + 2, 2, 1)
    s.put(SIGN_X - 1, 11, T["led_l"])
    s.put(SIGN_X + SIGN_W, 11, T["led_r"])
    for x in range(SIGN_X, SIGN_X + SIGN_W):
        s.put(x, 11, T["led_m"])
    for x in range(SIGN_X - 1, SIGN_X + SIGN_W + 1):
        s.put(x, 10, T["black"])
    s.palette(0, 12, 32, 6, 0)
    return s


# --------------------------------------------------------------------
# Sprites (CHR page 1)
# --------------------------------------------------------------------

PLAYER = [
    # 16x32, colors: 1 outline/hair, 2 skin, 3 jacket.
    "......1111......",
    ".....111111.....",
    "....11111111....",
    "....11122221....",
    "....1122.221....",
    "....1222222.....",
    ".....122221.....",
    "......1221......",
    ".....133331.....",
    "....13333331....",
    "...1333333331...",
    "...1333333331...",
    "...1313333131...",
    "...1313333131...",
    "...1313333131...",
    "...1313333131...",
    "...1213333121...",
    "...1213333121...",
    "....11333311....",
    "....11111111....",
    "....11111111....",
    "....111..111....",
    "....111..111....",
    "....111..111....",
    "....111..111....",
    "....111..111....",
    "....111..111....",
    "....111..111....",
    "....111..111....",
    "....111..111....",
    "...1111..1111...",
    "...1111..1111...",
]


def walk_frame(base, phase):
    """Swap the leg rows for a walk pose."""
    rows = list(base)
    legs = {
        1: ["....111..111....", "...111...111....", "...111....111...",
            "..111.....111...", "..111......111..", ".111.......111..",
            ".111........111.", "1111........1111", "1111........1111",
            "................", "................", "................"],
        2: ["....111..111....", "....111.111.....", ".....111111.....",
            ".....11111......", "......1111......", "......1111......",
            "......1111......", "......1111......", "......1111......",
            "......1111......", ".....11111......", ".....111111....."],
    }
    if phase in legs:
        rows[20:32] = legs[phase]
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
    post = ["..1231..", "..1231..", "..1231..", "..1231..",
            "..1231..", "..1231..", "..1231..", "..1231.."]
    T["post"] = page.add([[int(c) if c != "." else 0 for c in r] for r in post], "post")
    seam_l = ["...12331", "...12331", "...12331", "...12331",
              "...12331", "...12331", "...12331", "...12331"]
    T["seam_l"] = page.add([[int(c) if c != "." else 0 for c in r] for r in seam_l], "seam_l")
    seam_r = ["13321...", "13321...", "13321...", "13321...",
              "13321...", "13321...", "13321...", "13321..."]
    T["seam_r"] = page.add([[int(c) if c != "." else 0 for c in r] for r in seam_r], "seam_r")
    return T


def emit_page(name, page_no, page):
    data = []
    for px in page.tiles[page.first:]:
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
    train = train_screen(TT, wall)

    spr = Page("sprites", 0, font=False)
    ST = build_sprites(spr)

    chr_out = ["// Generated by examples/subway/tools/gen_gfx.py. Do not edit by hand.", ""]
    chr_out.append(emit_page("PlatformTiles", 0, plat))
    chr_out.append(emit_page("SpriteTiles", 1, spr))
    with open(os.path.join(out_dir, "gfx_chr.ne"), "w") as f:
        f.write("\n".join(chr_out))

    scr = ["// Generated by examples/subway/tools/gen_gfx.py. Do not edit by hand.", ""]
    scr.append(table("NT_PLATFORM", wall.bytes()))
    scr.append(table("NT_TRAIN", train.bytes()))
    with open(os.path.join(out_dir, "gfx_screens.ne"), "w") as f:
        f.write("\n".join(scr))

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
    consts.append(f"const FONT_BASE: u8 = {FONT_BASE}")
    consts.append(f"const S_POST: u8 = {ST['post']}")
    consts.append(f"const S_SEAM_L: u8 = {ST['seam_l']}")
    consts.append(f"const S_SEAM_R: u8 = {ST['seam_r']}")
    with open(os.path.join(out_dir, "gfx_consts.ne"), "w") as f:
        f.write("\n".join(consts) + "\n")
    print(f"platform page: {len(plat.tiles)} tiles, sprites: {len(spr.tiles)} tiles",
          file=sys.stderr)


if __name__ == "__main__":
    main()
