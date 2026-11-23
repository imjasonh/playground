#!/usr/bin/env python3
"""Generate original pixel-art PNG sprites and tileset for One Tap Quest.

Uses only Python's standard library (struct + zlib) so assets can be
regenerated deterministically on any machine with no extra dependencies.
"""

import os
import struct
import zlib

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SPRITES_DIR = os.path.join(ROOT, "assets", "sprites")
TILES_DIR = os.path.join(ROOT, "assets", "tiles")

TRANSPARENT = (0, 0, 0, 0)


def write_png(path, width, height, pixels):
    """Write an RGBA pixel list (row-major, tuples of 4 ints) as a PNG."""
    os.makedirs(os.path.dirname(path), exist_ok=True)
    raw = bytearray()
    for y in range(height):
        raw.append(0)  # filter type None
        row_start = y * width
        for x in range(width):
            r, g, b, a = pixels[row_start + x]
            raw.extend((r, g, b, a))

    def chunk(tag, data):
        crc = zlib.crc32(tag + data) & 0xFFFFFFFF
        return struct.pack(">I", len(data)) + tag + data + struct.pack(">I", crc)

    ihdr = struct.pack(">IIBBBBB", width, height, 8, 6, 0, 0, 0)
    idat = zlib.compress(bytes(raw), 9)
    png = b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", ihdr) + chunk(b"IDAT", idat) + chunk(b"IEND", b"")
    with open(path, "wb") as fp:
        fp.write(png)


def parse_art(lines, palette):
    """Convert ASCII pixel art rows + palette dict into (w, h, pixels)."""
    h = len(lines)
    w = len(lines[0])
    pixels = []
    for row in lines:
        assert len(row) == w, f"Row length mismatch: expected {w}, got {len(row)}: {row!r}"
        for ch in row:
            pixels.append(palette[ch])
    return w, h, pixels


def save_art(rel_dir, name, lines, palette):
    w, h, pixels = parse_art(lines, palette)
    write_png(os.path.join(rel_dir, name), w, h, pixels)


def concat_frames(frames):
    """Horizontally concatenate [(w, h, pixels), ...] into a sprite sheet."""
    fw, fh, _ = frames[0]
    total_w = fw * len(frames)
    out = [TRANSPARENT] * (total_w * fh)
    for idx, (w, h, pix) in enumerate(frames):
        assert w == fw and h == fh
        for y in range(fh):
            for x in range(fw):
                out[y * total_w + idx * fw + x] = pix[y * fw + x]
    return total_w, fh, out


# Palette colors (retro 16-bit RPG palette)
P = {
    ".": TRANSPARENT,
    "k": (24, 20, 37, 255),      # dark outline
    "w": (248, 248, 248, 255),   # white
    "s": (255, 212, 163, 255),   # skin
    "S": (214, 152, 108, 255),   # shaded skin
    "r": (228, 59, 68, 255),     # red
    "R": (158, 40, 53, 255),     # dark red
    "o": (247, 118, 34, 255),    # orange
    "y": (254, 231, 97, 255),    # yellow / gold
    "Y": (217, 160, 40, 255),    # dark gold
    "g": (99, 199, 77, 255),     # green
    "G": (62, 137, 72, 255),     # dark green
    "l": (168, 230, 100, 255),   # light green
    "b": (44, 138, 224, 255),    # blue
    "B": (29, 76, 158, 255),     # dark blue
    "c": (115, 239, 247, 255),   # cyan
    "C": (44, 184, 214, 255),    # dark cyan
    "p": (162, 75, 210, 255),    # purple
    "P": (104, 43, 140, 255),    # dark purple
    "m": (184, 111, 80, 255),    # brown
    "M": (116, 63, 57, 255),     # dark brown
    "a": (192, 203, 220, 255),   # silver / light gray
    "A": (139, 155, 180, 255),   # mid gray
    "d": (90, 105, 136, 255),    # dark gray
    "D": (58, 68, 102, 255),     # steel shadow
    "x": (24, 20, 37, 130),      # translucent shadow
}


def generate_sprites():
    # 1. Player (12x12) - blue-armored hero with cape & sword
    hero = [
        "....kkkk....",
        "...kbbbbk...",
        "..kbbwwbbk..",
        "..kssssssk..",
        "..kskssksk..",
        "...kssssk...",
        "..krbbbbrk..",
        ".krrbbbbraw.",
        ".krkbbbbk.k.",
        "...kBBBBk...",
        "...kMk.kMk..",
        "...kkk.kkk..",
    ]
    save_art(SPRITES_DIR, "player.png", hero, P)

    # 2. Party (36x12) - Warrior (left), Hero (center), Mage (right)
    warrior = [
        "....kkkk....",
        "...kaaaak...",
        "..kaaaaaak..",
        "..kssssssk..",
        "..kskssksk..",
        "...kssssk...",
        "..kRrrrrRk..",
        ".kYRrrrrrk..",
        ".kYkrrrrk...",
        "...kRRRRk...",
        "...kMk.kMk..",
        "...kkk.kkk..",
    ]
    mage = [
        ".....kk.....",
        "....kppk....",
        "...kppppk...",
        "..kppppppk..",
        "..kskssksk..",
        "...kssssk...",
        "..kPppppPk..",
        "..kppppppky.",
        "...kppppk.k.",
        "...kPPPPk...",
        "...kMk.kMk..",
        "...kkk.kkk..",
    ]
    party_lines = [warrior[i] + hero[i] + mage[i] for i in range(12)]
    save_art(SPRITES_DIR, "player_party.png", party_lines, P)

    # 3. Slime (12x12, LV 1) - bouncy cyan-blue slime
    slime = [
        "............",
        "............",
        "....kkkk....",
        "..kkcccckk..",
        ".kccwccccck.",
        ".kcwcccccck.",
        "kcckcccckcck",
        "kcckcccckcck",
        "kCCCCCCCCCCk",
        ".kCCCCCCCCk.",
        "..kkkkkkkk..",
        "............",
    ]
    save_art(SPRITES_DIR, "enemy_slime.png", slime, P)

    # 4. Snake (12x12, LV 2) - coiled emerald viper
    snake = [
        "....kkkk....",
        "...kggggk...",
        "..kgkggkgk..",
        "..kggggggk..",
        "...kgrrgk...",
        "....kggk....",
        "..kkggggkk..",
        ".kggGGGGggk.",
        "kggkGGGGkggk",
        "kGGkggggkGGk",
        ".kkGGGGGGkk.",
        "...kkkkkk...",
    ]
    save_art(SPRITES_DIR, "enemy_snake.png", snake, P)

    # 5. Bandit (14x14, LV 3) - hooded rogue with bandana & dagger
    bandit = [
        "....kkkkkk....",
        "...kMMMMMMk...",
        "..kMMMMMMMMk..",
        "..kskssssksk..",
        "..krrrrrrrrk..",
        "...kRRRRRRk...",
        "..kMMmmmmMMk..",
        ".kMMmmmmmmMMk.",
        ".kskmmmmmmkwa.",
        "..k.kmmmmk.k..",
        "....kddddk....",
        "...kdd..ddk...",
        "...kMk..kMk...",
        "...kkk..kkk...",
    ]
    save_art(SPRITES_DIR, "enemy_bandit.png", bandit, P)

    # 6. Goblin (14x14, LV 6) - horned green goblin with club
    goblin = [
        "..kk......kk..",
        ".kggkkkkkkggk.",
        "..kggggggggk..",
        "..kgwkgkwggk..",
        "..kggggggggk..",
        "...kgwwwwgk...",
        "..kMGGGGGGMk..",
        ".kMMGggggGMMk.",
        ".kM.kggggk.Mk.",
        "....kmmmmk....",
        "...kmm..mmk...",
        "...kGg..gGk...",
        "...kGG..GGk...",
        "...kkk..kkk...",
    ]
    save_art(SPRITES_DIR, "enemy_goblin.png", goblin, P)

    # 7. Golem (16x16, LV 7) - heavy stone golem with glowing eyes
    golem = [
        "....kkkkkkkk....",
        "...kAAaaaaAAk...",
        "..kAaaaaaaaaAk..",
        "..kAakyykyaAAk..",
        "..kAAaaaaAAAAk..",
        ".kkddAAAAAAddkk.",
        "kAAAdAAAAAAdAAAk",
        "kAAAdAAddAAdAAAk",
        "kAAAdddddddddAAk",
        "kAAkdAAAAAAdkAAk",
        ".kk.kddAAddk.kk.",
        "....kddddddk....",
        "...kddd..dddk...",
        "...kddd..dddk...",
        "...kDDD..DDDk...",
        "...kkkk..kkkk...",
    ]
    save_art(SPRITES_DIR, "enemy_golem.png", golem, P)

    # 8. Minotaur (16x16, LV 8) - horned bull warrior
    minotaur = [
        ".kk..........kk.",
        "kwwk..kkkk..kwwk",
        "kwwkkmmmmmmkkwwk",
        ".kkkmmmmmmmmkkk.",
        "...kmmrkmrmmk...",
        "...kmmmmmmmmk...",
        "...kmmYYYYmmk...",
        "..kMMmmmmmmMMk..",
        ".kMMmMMMMMMmMMk.",
        ".kmmkMMMMMMkmmk.",
        ".kmmkmmYYmmkmmk.",
        "..kk.kmmmmk.kk..",
        "....kmm..mmk....",
        "...kMMk..kMMk...",
        "...kDDk..kDDk...",
        "...kkkk..kkkk...",
    ]
    save_art(SPRITES_DIR, "enemy_minotaur.png", minotaur, P)

    # 9. Iron Knight (20x20, LV 9) - towering steel dark knight
    iron = [
        "........kkkk........",
        ".......krrrrk.......",
        "......krrrrrrk......",
        ".....kAAAAAAAAk.....",
        "....kAAaaaaaaAAk....",
        "....kAAkkkkkkAAk....",
        "....kAAkrcrckAAk....",
        "....kAAkkkkkkAAk....",
        "...kDDAAAAAAAAADk...",
        "..kDDDAAaaaaAADDDk..",
        ".kDDdkAAAAAAAAkdDDk.",
        ".kDDdkAAaaaaAAkdDDk.",
        ".kDDdkDDAAAADDkdDDk.",
        "..kkk.kDDDDDDk.kkk..",
        "......kDDyyDDk......",
        ".....kDDD..DDDk.....",
        ".....kDDk..kDDk.....",
        "....kDDDk..kDDDk....",
        "....kDDDk..kDDDk....",
        "....kkkkk..kkkkk....",
    ]
    save_art(SPRITES_DIR, "enemy_iron.png", iron, P)

    # 10. Dragon (32x24, LV 10) - crimson winged wyrm
    dragon = [
        "..........kk........kk..........",
        ".........kRRk......kRRk.........",
        "....kkkk.krrk.kkkk.krrk.kkkk....",
        "..kkRRRRkkrrkkrrrrkkrrkkRRRRkk..",
        ".kRRrrrrRRrrrrrrrrrrrrRRrrrrRRk.",
        "kRRrrrrrrRRrrrrrrrrrrRRrrrrrrRRk",
        "kRrrrRRrrrRRrryrryrrRRrrrRRrrrRk",
        "kRrrRRRRrrrRrrrrrrrrRrrrRRRRrrRk",
        ".kRRrrrrrRRrrrrrrrrrrRRrrrrrRRk.",
        "..kRRrrrRRrrrroorrrrrrRRrrrRRk..",
        "...kkRRRkkrrrooooorrrrkkRRRkk...",
        ".....kkk..krrryyyyrrrk..kkk.....",
        ".........krrryyyyyyrrrk.........",
        "........krrrryyyyyyrrrrk........",
        "........krrrryyyyyyrrrrk........",
        ".......kRRrrryyyyyyrrrRRk.......",
        ".......kRRrrrryyyyrrrrRRk.......",
        "........kRRrrrrrrrrrrRRk........",
        "........kRRkrrrrrrrrkRRk........",
        ".......kRRk..krrrrk..kRRk.......",
        ".......kwwk..kRRRk...kwwk.......",
        ".......kkk...kRRk.....kkk.......",
        ".............kRk................",
        "..............k.................",
    ]
    save_art(SPRITES_DIR, "enemy_dragon.png", dragon, P)

    # 11. Boss (40x40) - Dark Overlord with crown, cape, and glowing eyes
    boss_px = [TRANSPARENT] * (40 * 40)

    def b_rect(x0, y0, x1, y1, col):
        for y in range(max(0, y0), min(40, y1)):
            for x in range(max(0, x0), min(40, x1)):
                boss_px[y * 40 + x] = col

    # Horns & crown
    b_rect(6, 2, 11, 12, P["k"])
    b_rect(7, 3, 10, 11, P["y"])
    b_rect(29, 2, 34, 12, P["k"])
    b_rect(30, 3, 33, 11, P["y"])
    b_rect(12, 4, 28, 10, P["k"])
    b_rect(13, 5, 27, 9, P["Y"])
    b_rect(18, 2, 22, 8, P["k"])
    b_rect(19, 3, 21, 7, P["r"])
    # Flowing purple cape
    b_rect(3, 14, 37, 38, P["k"])
    b_rect(5, 16, 35, 36, P["P"])
    b_rect(7, 17, 33, 35, P["p"])
    # Armored torso
    b_rect(10, 18, 30, 35, P["k"])
    b_rect(11, 19, 29, 34, P["D"])
    b_rect(13, 20, 27, 32, P["d"])
    # Chest gem
    b_rect(17, 22, 23, 28, P["k"])
    b_rect(18, 23, 22, 27, P["r"])
    b_rect(19, 24, 21, 26, P["y"])
    # Head / helm
    b_rect(11, 8, 29, 20, P["k"])
    b_rect(12, 9, 28, 19, P["D"])
    b_rect(13, 10, 27, 18, P["k"])
    # Glowing eyes
    b_rect(15, 12, 18, 15, P["r"])
    b_rect(16, 13, 17, 14, P["y"])
    b_rect(22, 12, 25, 15, P["r"])
    b_rect(23, 13, 24, 14, P["y"])
    # Shoulder pauldrons
    b_rect(5, 16, 13, 24, P["k"])
    b_rect(6, 17, 12, 23, P["A"])
    b_rect(7, 18, 11, 21, P["a"])
    b_rect(27, 16, 35, 24, P["k"])
    b_rect(28, 17, 34, 23, P["A"])
    b_rect(29, 18, 33, 21, P["a"])
    # Claws
    b_rect(4, 25, 10, 31, P["k"])
    b_rect(5, 26, 9, 30, P["a"])
    b_rect(30, 25, 36, 31, P["k"])
    b_rect(31, 26, 35, 30, P["a"])
    # Boots
    b_rect(12, 34, 18, 39, P["k"])
    b_rect(13, 35, 17, 38, P["d"])
    b_rect(22, 34, 28, 39, P["k"])
    b_rect(23, 35, 27, 38, P["d"])
    write_png(os.path.join(SPRITES_DIR, "enemy_boss.png"), 40, 40, boss_px)

    # 12. Boss HP Crystal (12x16)
    crystal = [
        ".....kk.....",
        "....kcck....",
        "...kcwwck...",
        "..kcwccCck..",
        ".kcwccccCck.",
        ".kccwcccCCk.",
        "kcccccccCCCk",
        "kcccccccCCCk",
        "kcccccccCCCk",
        "kccCccccCCCk",
        ".kCCcccCCCk.",
        ".kCCCCCCCCk.",
        "..kCCCCCCk..",
        "...kCCCCk...",
        "....kCCk....",
        ".....kk.....",
    ]
    save_art(SPRITES_DIR, "boss_crystal.png", crystal, P)

    # 13. Boss Crystal Shadow (12x3)
    shadow = [
        "..xxxxxxxx..",
        ".xxxxxxxxxx.",
        "..xxxxxxxx..",
    ]
    save_art(SPRITES_DIR, "boss_crystal_shadow.png", shadow, P)

    # 14. Item: Sword (14x14)
    sword = [
        "..........kkk.",
        ".........kwwk.",
        "........kwwak.",
        ".......kwwak..",
        "......kwwak...",
        ".....kwwak....",
        "....kwwak.....",
        "..kkwwak......",
        ".kYYyak.......",
        "..kYYk........",
        "..kMYk........",
        ".kMMk.........",
        ".kYk..........",
        "..k...........",
    ]
    save_art(SPRITES_DIR, "item_sword.png", sword, P)

    # 15. Item: Shield (14x14)
    shield = [
        "..kkkkkkkkkk..",
        ".kYYYYYYYYYYk.",
        ".kYbbbbbbbbYk.",
        ".kYbbbyybbbYk.",
        ".kYbbbyybbbYk.",
        ".kYbyyyyyybYk.",
        ".kYbyyyyyybYk.",
        ".kYbbbyybbbYk.",
        "..kYbbbyybYk..",
        "..kYbbbyybYk..",
        "...kYbbbbYk...",
        "....kYbbYk....",
        ".....kYYk.....",
        "......kk......",
    ]
    save_art(SPRITES_DIR, "item_shield.png", shield, P)

    # 16. Item: Thunder (14x14) - glowing lightning bolt orb
    thunder = [
        "....kkkkkk....",
        "..kkBBBBBBkk..",
        ".kBBccyyccBBk.",
        ".kBccyyyyccBk.",
        "kBccyywwycccBk",
        "kBcyywwyycccBk",
        "kBcyyyyyyyccBk",
        "kBccccyyyyccBk",
        "kBcccyywwyccBk",
        "kBccyywwycccBk",
        ".kBccyyccccBk.",
        ".kBBccccccBBk.",
        "..kkBBBBBBkk..",
        "....kkkkkk....",
    ]
    save_art(SPRITES_DIR, "item_thunder.png", thunder, P)

    # 17. Item: Warp (14x14) - swirling magenta/cyan portal
    warp = [
        "....kkkkkk....",
        "..kkppppppkk..",
        ".kppccccccppk.",
        ".kpccppppccpk.",
        "kpccppwwppccpk",
        "kpcppwwwwppcpk",
        "kpcpwwccwwpcpk",
        "kpcpwwccwwpcpk",
        "kpcppwwwwppcpk",
        "kpccppwwppccpk",
        ".kpccppppccpk.",
        ".kppccccccppk.",
        "..kkppppppkk..",
        "....kkkkkk....",
    ]
    save_art(SPRITES_DIR, "item_warp.png", warp, P)

    # 18. Item: Join (14x14) - iconic foaming tavern ale mug!
    join = [
        "...kkkkkkkk...",
        "..kwwwwwwwwk..",
        ".kwwwwwawwwwk.",
        "..kwwwwwwwwk..",
        "..kYYYYYYYYkk.",
        "..kYyyYYyyYkYk",
        "..kYyyYYyyYkYk",
        "..kYyyYYyyYkYk",
        "..kYyyYYyyYkYk",
        "..kYyyYYyyYkk.",
        "..kYyyyyyyYk..",
        "..kYYYYYYYYk..",
        "..kkkkkkkkkk..",
        "..............",
    ]
    save_art(SPRITES_DIR, "item_join.png", join, P)

    # 19. Magic Thunder Projectile (12x12)
    magic_t = [
        "....kkkk....",
        "...kcyyck...",
        "..kcywwyck..",
        ".kcywwwwyck.",
        "kcywwyywwyck",
        "kcywyyyywyck",
        "kcywyyyywyck",
        "kcywwyywwyck",
        ".kcywwwwyck.",
        "..kcywwyck..",
        "...kcyyck...",
        "....kkkk....",
    ]
    save_art(SPRITES_DIR, "magic_thunder.png", magic_t, P)

    # 20. Effect: Kill (5 frames of 16x16 = 80x16)
    kill_frames = []
    for f in range(5):
        px = [TRANSPARENT] * (16 * 16)
        cx, cy = 7.5, 7.5
        r_outer = 3.0 + f * 1.4
        r_inner = max(0.0, (f - 1) * 1.6)
        for y in range(16):
            for x in range(16):
                dist = ((x - cx) ** 2 + (y - cy) ** 2) ** 0.5
                if r_inner <= dist <= r_outer:
                    if f == 0:
                        px[y * 16 + x] = P["w"]
                    elif f == 1:
                        px[y * 16 + x] = P["y"] if dist < r_outer - 1 else P["o"]
                    elif f == 2:
                        px[y * 16 + x] = P["o"] if dist < r_outer - 1.2 else P["r"]
                    elif f == 3:
                        if (x + y) % 2 == 0:
                            px[y * 16 + x] = P["r"]
                    else:
                        if (x * 3 + y * 5) % 4 == 0:
                            px[y * 16 + x] = P["R"]
        kill_frames.append((16, 16, px))
    kw, kh, kpix = concat_frames(kill_frames)
    write_png(os.path.join(SPRITES_DIR, "effect_kill.png"), kw, kh, kpix)

    # 21. Effect: Item pickup sparkle (4 frames of 14x14 = 56x14)
    item_frames = []
    for f in range(4):
        px = [TRANSPARENT] * (14 * 14)
        cx, cy = 6, 6
        arm = 2 + f * 2
        for d in range(-arm, arm + 1):
            col = P["w"] if abs(d) < arm - 1 else P["y"]
            if f == 3 and abs(d) < 3:
                continue
            for tx, ty in ((cx + d, cy), (cx, cy + d)):
                if 0 <= tx < 14 and 0 <= ty < 14:
                    px[ty * 14 + tx] = col
        # diagonal sparks
        diag = 1 + f
        for sx, sy in ((-diag, -diag), (diag, -diag), (-diag, diag), (diag, diag)):
            tx, ty = cx + sx, cy + sy
            if 0 <= tx < 14 and 0 <= ty < 14:
                px[ty * 14 + tx] = P["c"]
        item_frames.append((14, 14, px))
    iw, ih, ipix = concat_frames(item_frames)
    write_png(os.path.join(SPRITES_DIR, "effect_item.png"), iw, ih, ipix)


def generate_tileset():
    """Generate a 6x1 strip of 16x16 tiles (96x16):
    0: grass, 1: grass_flower, 2: sand_path, 3: water, 4: stone_floor, 5: castle_wall
    """
    tiles = []

    # 0: Grass
    t = []
    for y in range(16):
        for x in range(16):
            if (x * 7 + y * 13) % 19 == 0:
                t.append((82, 168, 72, 255))
            elif (x * 11 + y * 5) % 23 == 0:
                t.append((124, 206, 94, 255))
            else:
                t.append((96, 184, 80, 255))
    tiles.append((16, 16, t))

    # 1: Grass with wildflowers / pebble
    t = list(tiles[0][2])
    for fx, fy, col in ((4, 5, P["y"]), (5, 5, P["w"]), (11, 10, P["c"]), (12, 10, P["w"]), (8, 13, P["g"])):
        t[fy * 16 + fx] = col
    tiles.append((16, 16, t))

    # 2: Sandy dirt / middle road
    t = []
    for y in range(16):
        for x in range(16):
            if (x * 5 + y * 9) % 17 == 0:
                t.append((196, 154, 104, 255))
            elif (x * 13 + y * 3) % 21 == 0:
                t.append((228, 194, 140, 255))
            else:
                t.append((212, 174, 120, 255))
    tiles.append((16, 16, t))

    # 3: Water pond
    t = []
    for y in range(16):
        for x in range(16):
            if y % 4 == 1 and (x + y) % 5 < 2:
                t.append((112, 204, 240, 255))
            else:
                t.append((54, 134, 206, 255))
    tiles.append((16, 16, t))

    # 4: Stone floor (castle / boss room)
    t = []
    for y in range(16):
        for x in range(16):
            mortar = (y % 8 == 0) or ((x + (4 if (y // 8) % 2 else 0)) % 8 == 0)
            if mortar:
                t.append((58, 62, 82, 255))
            elif (x + y) % 11 == 0:
                t.append((96, 102, 128, 255))
            else:
                t.append((80, 86, 110, 255))
    tiles.append((16, 16, t))

    # 5: Castle wall / dark brick
    t = []
    for y in range(16):
        for x in range(16):
            mortar = (y % 4 == 0) or ((x + (4 if (y // 4) % 2 else 0)) % 8 == 0)
            if mortar:
                t.append((28, 26, 42, 255))
            elif y % 4 == 1:
                t.append((66, 66, 92, 255))
            else:
                t.append((46, 46, 68, 255))
    tiles.append((16, 16, t))

    tw, th, tpix = concat_frames(tiles)
    write_png(os.path.join(TILES_DIR, "map_tiles.png"), tw, th, tpix)


if __name__ == "__main__":
    generate_sprites()
    generate_tileset()
    print(f"Generated sprites in {SPRITES_DIR} and tileset in {TILES_DIR}")
