#!/usr/bin/env python3
"""Generate the data files for examples/rampart.ne.

Writes three files under examples/rampart/:

  assets.ne       the Tileset sprite: every CHR tile the game uses
  backgrounds.ne  the Title, Board, and Card nametables
  text.ne         string tables and their S_* ids

Tile indices equal ASCII codes for text, so the string tables hold
plain ASCII bytes. The font comes from examples/sha256/assets.ne.

Run from nescript/:  python3 scripts/gen_rampart.py
"""

import os
import re

import rampart_art as art

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "examples", "rampart")
SHA_ASSETS = os.path.join(ROOT, "examples", "sha256", "assets.ne")

BLANK = ["........"] * 8


def load_sha_font():
    """Map characters to 8-row glyphs from the sha256 tileset."""
    text = open(SHA_ASSETS).read()
    names = {}
    for i, ch in enumerate("ABCDEFGHIJKLMNOPQRSTUVWXYZ"):
        names[i + 1] = ch
    for i, ch in enumerate("0123456789"):
        names[27 + i] = ch
    names[38] = "."
    names[39] = ":"
    names[40] = "-"
    glyphs = {}
    blocks = re.split(r"// ── (\d+):", text)
    for k in range(1, len(blocks), 2):
        idx = int(blocks[k])
        rows = re.findall(r'"([.0-3#%@]{8})"', blocks[k + 1])[:8]
        if idx in names and len(rows) == 8:
            # Text draws in palette colour 3 so every sub-palette's
            # brightest colour carries the glyph.
            glyphs[names[idx]] = [r.replace("2", "3") for r in rows]
    return glyphs


EXTRA_GLYPHS = {
    "/": [
        "........",
        ".....33.",
        "....33..",
        "...33...",
        "..33....",
        ".33.....",
        "33......",
        "........",
    ],
    ">": [
        "........",
        ".33.....",
        "..33....",
        "...33...",
        "..33....",
        ".33.....",
        "........",
        "........",
    ],
    "+": [
        "........",
        "...33...",
        "...33...",
        ".333333.",
        "...33...",
        "...33...",
        "........",
        "........",
    ],
    "!": [
        "........",
        "...33...",
        "...33...",
        "...33...",
        "...33...",
        "........",
        "...33...",
        "........",
    ],
    "?": [
        "........",
        "..3333..",
        ".33..33.",
        "....33..",
        "...33...",
        "........",
        "...33...",
        "........",
    ],
    "=": [
        "........",
        "........",
        ".333333.",
        "........",
        ".333333.",
        "........",
        "........",
        "........",
    ],
    "*": [
        "........",
        "........",
        "..3333..",
        "..3333..",
        "..3333..",
        "..3333..",
        "........",
        "........",
    ],
}


# Tile numbers the .ne sources refer to by name.
T_FLOOR = 1  # 1..4
T_RUIN = 5  # 5..8
T_LOGO = 12
T_CORNER = 13
T_AIM = 14
T_BURST = 15
T_SCUFF = 16
T_HOLES = 17
T_FIRE = 18  # 18..19, two frames
T_CRATER = 20
T_ARROW = 21
T_ACT = 22  # 22..28, one icon per action, in action order
T_PIKE = 96  # 96..99
T_MAUL = 100  # 100..103
# Weapon pictures, two tiles each, in weapon-id order. The order
# matches WPN_TILE in examples/rampart/constants.ne.
WPN_AT = [(104, 105), (110, 111), (9, 10), (108, 109), (11, 29)]
# Body-plate portraits: frame f, cell c is tile T_PLATE + f * 72 + c,
# and its charred copy for a wrecked location is 36 tiles later.
T_PLATE = 112
TILE_COUNT = 256

# Board square, drawn inset by one pixel so neighbours show a gap.
FLOOR = [
    "................",
    ".11111111111111.",
    ".1............1.",
    ".1............1.",
    ".1............1.",
    ".1............1.",
    ".1.....11.....1.",
    ".1....1..1....1.",
    ".1....1..1....1.",
    ".1.....11.....1.",
    ".1............1.",
    ".1............1.",
    ".1............1.",
    ".1............1.",
    ".11111111111111.",
    "................",
]

RUIN = [
    "................",
    ".11111111111111.",
    ".1..2222.....21.",
    ".1.233332...231.",
    ".1.233332..2331.",
    ".1..2222...2321.",
    ".1.......22.221.",
    ".12.....2332..1.",
    ".132...23333221.",
    ".1332..2333332..",
    ".12222.2222222..",
    ".1..22222......1",
    ".1.2333332.....1",
    ".1.23333332....1",
    ".11222222221111.",
    "................",
]

ARROW = [
    "........",
    ".33.....",
    ".3333...",
    ".333333.",
    ".3333...",
    ".33.....",
    "........",
    "........",
]
LOGO = [
    "33333333",
    "32222221",
    "32222221",
    "32222221",
    "32222221",
    "32222221",
    "32222221",
    "11111111",
]


def build_tiles():
    font = load_sha_font()
    font.update(EXTRA_GLYPHS)
    tiles = [BLANK] * TILE_COUNT
    for i, t in enumerate(art.split16(FLOOR)):
        tiles[T_FLOOR + i] = t
    for i, t in enumerate(art.split16(RUIN)):
        tiles[T_RUIN + i] = t
    tiles[T_LOGO] = LOGO
    for ch, rows in font.items():
        tiles[ord(ch)] = rows
    tiles[T_CORNER] = art.CORNER
    tiles[T_AIM] = art.AIM
    tiles[T_BURST] = art.BURST
    tiles[T_SCUFF] = art.SCUFF
    tiles[T_HOLES] = art.HOLES
    tiles[T_FIRE] = art.FIRE_A
    tiles[T_FIRE + 1] = art.FIRE_B
    tiles[T_CRATER] = art.CRATER
    tiles[T_ARROW] = ARROW
    for i, t in enumerate(art.ACTIONS):
        tiles[T_ACT + i] = t
    for i, pic in enumerate(art.WEAPONS):
        left, right = art.pair(pic)
        a, b = WPN_AT[i]
        tiles[a] = left
        tiles[b] = right
    for i, t in enumerate(art.split16(art.PIKE_MINI)):
        tiles[T_PIKE + i] = t
    for i, t in enumerate(art.split16(art.MAUL_MINI)):
        tiles[T_MAUL + i] = t
    for f, pic in enumerate([art.pike(), art.maul()]):
        base = T_PLATE + f * 72
        for c, t in enumerate(art.tiles_of(pic, 6, 6)):
            tiles[base + c] = t
        for c, t in enumerate(art.tiles_of(art.charred(pic), 6, 6)):
            tiles[base + 36 + c] = t
    return tiles


def tile_label(i):
    wpn_names = ["thermal lance", "gatling cannon", "missile pod", "sword", "hammer"]
    for n, (a, b) in enumerate(WPN_AT):
        if i == a:
            return f"weapon: {wpn_names[n]} left"
        if i == b:
            return f"weapon: {wpn_names[n]} right"
    if 32 < i < 127 and chr(i).isprintable():
        return repr(chr(i))
    if i >= T_PLATE:
        f, rest = divmod(i - T_PLATE, 72)
        kind, cell = divmod(rest, 36)
        name = ["pike", "maul"][f] + [" plate", " charred plate"][kind]
        return f"{name} cell {cell}"
    return {
        0: "reserved",
        32: "space",
        T_FLOOR: "floor TL",
        T_FLOOR + 1: "floor TR",
        T_FLOOR + 2: "floor BL",
        T_FLOOR + 3: "floor BR",
        T_RUIN: "ruin TL",
        T_RUIN + 1: "ruin TR",
        T_RUIN + 2: "ruin BL",
        T_RUIN + 3: "ruin BR",
        T_LOGO: "logo block",
        T_CORNER: "square cursor corner",
        T_AIM: "aim brackets",
        T_BURST: "impact flash",
        T_SCUFF: "decal: scuffs",
        T_HOLES: "decal: holes",
        T_FIRE: "decal: fire, frame 1",
        T_FIRE + 1: "decal: fire, frame 2",
        T_CRATER: "decal: crater",
        T_ARROW: "menu arrow",
        T_ACT: "action: snap",
        T_ACT + 1: "action: step",
        T_ACT + 2: "action: shield",
        T_ACT + 3: "action: standard",
        T_ACT + 4: "action: rush",
        T_ACT + 5: "action: aimed",
        T_ACT + 6: "action: charge",
        T_PIKE: "pike TL",
        T_PIKE + 1: "pike TR",
        T_PIKE + 2: "pike BL",
        T_PIKE + 3: "pike BR",
        T_MAUL: "maul TL",
        T_MAUL + 1: "maul TR",
        T_MAUL + 2: "maul BL",
        T_MAUL + 3: "maul BR",
    }.get(i, "unused")


def write_assets(tiles):
    out = [
        "// rampart/assets.ne: the Tileset sprite. Generated by",
        "// scripts/gen_rampart.py; edit the generator, not this file.",
        "//",
        "// Background and sprites share this one pattern table. Text",
        "// tiles sit at their ASCII codes, so string bytes are tile",
        "// numbers. Tile 0 is the compiler's reserved smiley; this",
        "// block starts at tile 1.",
        "",
        "sprite Tileset {",
        "    pixels: [",
    ]
    for i in range(1, len(tiles)):
        out.append(f"        // {i}: {tile_label(i)}")
        for row in tiles[i]:
            out.append(f'        "{row}",')
    out[-1] = out[-1].rstrip(",")
    out += ["    ]", "}", ""]
    open(os.path.join(OUT, "assets.ne"), "w").write("\n".join(out))


# 3x5 block letters for the title logo.
BIG = {
    "R": ["##.", "#.#", "##.", "#.#", "#.#"],
    "A": [".#.", "#.#", "###", "#.#", "#.#"],
    "M": ["#.#", "###", "###", "#.#", "#.#"],
    "P": ["##.", "#.#", "##.", "#..", "#.."],
    "T": ["###", ".#.", ".#.", ".#.", ".#."],
}


def legend_for(rows, extra):
    chars = sorted({ch for row in rows for ch in row})
    lines = []
    for ch in chars:
        if ch in extra:
            lines.append(f'        "{ch}": {extra[ch]}')
        else:
            lines.append(f'        "{ch}": {ord(ch)}')
    return lines


def background(name, rows, extra, palette_map):
    rows = [r.ljust(32) for r in rows]
    assert len(rows) <= 30 and all(len(r) == 32 for r in rows), name
    out = [f"background {name} {{", "    legend {"]
    out += legend_for(rows, extra)
    out += ["    }", "    map: ["]
    out += [f'        "{r}",' for r in rows]
    out[-1] = out[-1].rstrip(",")
    out += ["    ]", "    palette_map: ["]
    out += [f'        "{r}",' for r in palette_map]
    out[-1] = out[-1].rstrip(",")
    out += ["    ]", "}", ""]
    return out


RUINS = [(4, 4), (4, 5), (5, 4), (7, 7), (7, 6), (6, 7)]

# Plans in card order: cost, then name. Index = two-press code
# (first press * 6 + second press, presses U D L R A B = 0..5).
ACTIONS = ["SNAP", "STEP", "SHIELD", "STANDARD", "RUSH", "AIMED", "CHARGE"]
COST = [1, 1, 1, 2, 2, 3, 3]
PLANS = [
    ["SNAP"],
    ["STEP"],
    ["SHIELD"],
    ["STANDARD"],
    ["RUSH"],
    ["SNAP", "STEP"],
    ["SNAP", "SHIELD"],
    ["STEP", "SHIELD"],
    ["AIMED"],
    ["CHARGE"],
    ["SNAP", "STANDARD"],
    ["SNAP", "RUSH"],
    ["STEP", "STANDARD"],
    ["STEP", "RUSH"],
    ["SHIELD", "STANDARD"],
    ["SHIELD", "RUSH"],
    ["SNAP", "STEP", "SHIELD"],
]
BUTTONS = "UDLRAB"


def plan_mask(p):
    m = 0
    for a in p:
        m |= 1 << ACTIONS.index(a)
    return m


def plan_cost(p):
    return sum(COST[ACTIONS.index(a)] for a in p)


def write_backgrounds():
    out = [
        "// rampart/backgrounds.ne: Title, Board, and Card nametables.",
        "// Generated by scripts/gen_rampart.py; edit the generator,",
        "// not this file.",
        "",
    ]

    # Title: block logo, then menu labels. Values are painted at
    # runtime next to each label.
    title = [""] * 30
    word = "RAMPART"
    width = len(word) * 4 - 1
    left = (32 - width) // 2
    for y in range(5):
        line = [" "] * 32
        for i, ch in enumerate(word):
            for x in range(3):
                if BIG[ch][y][x] == "#":
                    line[left + i * 4 + x] = "#"
        title[4 + y] = "".join(line)
    title[13] = "    MODE"
    title[15] = "    CPU"
    title[17] = "    P1 MECH"
    title[19] = "    P2 MECH"
    title[21] = "    START"
    # Rows 23..28 hold each player's mech portrait, painted at
    # runtime: P1 at columns 2..7 in bg2, P2 at 24..29 in bg3.
    portraits = "0" + "222" + "0" * 8 + "333" + "0"
    title_pal = ["0" * 16] * 2 + ["3" * 16] * 3 + ["0" * 16] * 6 + [portraits] * 4
    out += background("Title", title, {"#": T_LOGO}, title_pal)

    # Board: 12x12 squares of 2x2 tiles at tile rows 2..25, columns
    # 1..24. The panel (columns 25..30) and the text rows are painted
    # at runtime. Columns 0 and 31 stay blank because TVs and most
    # emulators crop them.
    board = [""] * 30
    for r in range(12):
        top = [" "]
        bottom = [" "]
        for c in range(12):
            if (c, r) in RUINS:
                top.append("ef")
                bottom.append("gh")
            else:
                top.append("ab")
                bottom.append("cd")
        board[2 + 2 * r] = "".join(top)
        board[3 + 2 * r] = "".join(bottom)
    board_extra = {
        "a": T_FLOOR,
        "b": T_FLOOR + 1,
        "c": T_FLOOR + 2,
        "d": T_FLOOR + 3,
        "e": T_RUIN,
        "f": T_RUIN + 1,
        "g": T_RUIN + 2,
        "h": T_RUIN + 3,
    }
    board_pal = (
        ["0" * 16]
        + ["0" * 12 + "2222"] * 6
        + ["0" * 12 + "3333"] * 6
        + ["0" * 16] * 2
    )
    out += background("Board", board, board_extra, board_pal)

    # Card: the plan list for the secret lock. The legal marks in the
    # P1 and P2 columns, the clock, and the READY lines are painted
    # at runtime.
    card = [""] * 30
    card[1] = " LOCK YOUR PLAN"
    card[3] = " KEY  PLAN             PT P1 P2"
    for i, p in enumerate(PLANS):
        code = BUTTONS[i // 6] + BUTTONS[i % 6]
        card[5 + i] = f"  {code}  {' '.join(p):<17}{plan_cost(p)}"
    card[23] = " U UP  D DOWN  L LEFT  R RIGHT"
    card[24] = " THE LAST TWO PRESSES COUNT"
    card[25] = " START WHEN DONE"
    card_pal = ["0" * 16] * 2 + ["0" * 13 + "230"] * 9 + ["0" * 16] * 4
    out += background("Card", card, {}, card_pal)

    open(os.path.join(OUT, "backgrounds.ne"), "w").write("\n".join(out))


# Every string the game prints at runtime. The id constant is S_<KEY>.
STRINGS = [
    ("TURN", "TURN"),
    ("RANGE", "RANGE"),
    ("COVER", "COVER"),
    ("PIKE", "PIKE"),
    ("MAUL", "MAUL"),
    ("HUMAN", "HUMAN"),
    ("CPU_EASY", "CPU EASY"),
    ("CPU_MED", "CPU MED"),
    ("CPU_HARD", "CPU HARD"),
    ("CRIT", "CRIT"),
    ("SHIELD_UP", "SHIELD"),
    ("LOCKED", "LOCKED"),
    ("A_SNAP", "SNAP"),
    ("A_STEP", "STEP"),
    ("A_SHIELD", "SHIELD"),
    ("A_STANDARD", "STANDARD"),
    ("A_RUSH", "RUSH"),
    ("A_AIMED", "AIMED"),
    ("A_CHARGE", "CHARGE"),
    ("W_LANCE", "THERMAL LANCE"),
    ("W_CANNON", "GATLING CANNON"),
    ("W_POD", "MISSILE POD"),
    ("W_SWORD", "SWORD"),
    ("W_HAMMER", "HAMMER"),
    ("L_HEAD", "HEAD"),
    ("L_GUN", "GUN"),
    ("L_SHIELD", "SHIELD"),
    ("L_ARML", "ARM L"),
    ("L_ARMR", "ARM R"),
    ("L_MAST", "MAST"),
    ("L_PAULL", "PAUL L"),
    ("L_PAULR", "PAUL R"),
    ("L_HULL", "HULL"),
    ("L_LEGL", "LEG L"),
    ("L_LEGR", "LEG R"),
    ("L_MISS", "OFF THE PLATE"),
    ("P1", "P1"),
    ("P2", "P2"),
    ("DICE", "DICE"),
    ("SAVE", "SAVE"),
    ("NEED", "NEED"),
    ("SAVED", "SAVED"),
    ("HIT", "HIT"),
    ("MISS", "MISS"),
    ("CRITICAL", "CRITICAL"),
    ("ALREADY", "ALREADY CRITICAL"),
    ("NO_GUN", "NO GUN IN RANGE"),
    ("NO_CONTACT", "NO CONTACT"),
    ("NO_ARM", "RIGHT ARM IS DOWN"),
    ("SQ", "SQ"),
    ("PICK_SQ", "PICK A SQUARE"),
    ("STAY", "STAYS PUT"),
    ("MOVES", "MOVES"),
    ("AIM_AT", "AIM AT"),
    ("REVEALED", "PLANS REVEALED"),
    ("CPU_LOCK", "CPUS LOCK THEIR PLANS"),
    ("FIRST", "GOES FIRST"),
    ("WINS", "WINS"),
    ("WRECKED", "IS WRECKED"),
    ("DRAW", "DRAW"),
    ("TIME_UP", "TURN LIMIT"),
    ("READY", "READY"),
    ("CPU", "CPU"),
    ("THINKING", "THINKING"),
    ("TIME", "TIME"),
    ("M_CPU2", "CPU VS CPU"),
    ("M_1P", "1P VS CPU"),
    ("M_2P", "2 PLAYERS"),
    ("D_EASY", "EASY"),
    ("D_MED", "MEDIUM"),
    ("D_HARD", "HARD"),
    ("PRESS_START", "PRESS START"),
    ("ROLL", "ROLL"),
    ("ACTION", "ACTION"),
    ("C_NAME", "NAME"),
    ("C_ARM", "ARM"),
    ("C_START", "START"),
    ("C_CLEAR", "B CLEAR"),
]


def write_text():
    chunks = [[]]
    chunk_of = []
    off_of = []
    for _, s in STRINGS:
        if len(chunks[-1]) + len(s) > 256:
            chunks.append([])
        chunk_of.append(len(chunks) - 1)
        off_of.append(len(chunks[-1]))
        chunks[-1].extend(ord(ch) for ch in s)
    assert len(chunks) <= 3, "str_byte in render.ne reads three chunks"
    out = [
        "// rampart/text.ne: string tables. Generated by",
        "// scripts/gen_rampart.py; edit the generator, not this file.",
        "//",
        "// Strings are ASCII bytes, which are also tile numbers. A",
        "// const array holds at most 256 bytes, so the strings are",
        "// packed into chunks and str_byte() in render.ne picks the",
        "// chunk.",
        "",
    ]
    for i, (key, s) in enumerate(STRINGS):
        out.append(f"const S_{key}: u8 = {i}")
    out.append("")

    def arr(name, values):
        body = ", ".join(str(v) for v in values)
        return f"const {name}: u8[{len(values)}] = [{body}]"

    out.append(arr("STR_CHUNK", chunk_of))
    out.append(arr("STR_OFF", off_of))
    out.append(arr("STR_LEN", [len(s) for _, s in STRINGS]))
    while len(chunks) < 3:
        chunks.append([32])
    for i, c in enumerate(chunks):
        out.append(arr(f"TXT{i}", c))
    out.append("")

    # Plan tables, in card order.
    out.append("// Plans: action bitmask (bit n = action n in resolve order)")
    out.append("// and point cost. The index is the two-press code.")
    out.append(arr("PLAN_MASK", [plan_mask(p) for p in PLANS]))
    out.append(arr("PLAN_COST", [plan_cost(p) for p in PLANS]))
    out.append("")
    open(os.path.join(OUT, "text.ne"), "w").write("\n".join(out))


def main():
    os.makedirs(OUT, exist_ok=True)
    write_assets(build_tiles())
    write_backgrounds()
    write_text()


if __name__ == "__main__":
    main()
