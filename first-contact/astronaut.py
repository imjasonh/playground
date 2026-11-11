"""Card 02 - THE ASTRONAUT.

A spacewalker drifts on a tether, one glove raised. The gold visor reflects the
magenta world below and a small waving figure - the Visitor from card 03 -
so the middle card is the moment the two archetypes see each other.
"""

from kit import (AMBER, CYAN, INK, MAGENTA, Card, card_frame, ellipse_path,
                 linear, radial, rrect_path, sky)

ACCENT = CYAN

SUIT = "#e8ebf2"
SUIT_DK = "#aeb6c8"
VISOR = "#2a1430"
GOLD = "#ffcf6e"
TRIM = "#ff7a4d"
SHADE = "#2c2a46"
RIM = "#dff4ff"


def shapes(card):
    card.shape("pack", {"type": "path", "d": rrect_path(372, 452, 280, 300, 70)})
    card.shape("torso", {"type": "path", "d": rrect_path(352, 470, 320, 360, 110)})
    card.shape("belt", {"type": "path", "d": rrect_path(360, 744, 304, 70, 34)})
    card.shape("chest", {"type": "path", "d": rrect_path(452, 548, 120, 110, 26)})
    # Legs tucked, drifting.
    card.shape("leg-l", {"type": "path", "d":
                         "M392 796 C 352 880 360 968 408 1016 L 486 988 "
                         "C 452 944 450 872 470 806 Z"})
    card.shape("leg-r", {"type": "path", "d":
                         "M560 806 C 600 880 614 964 578 1020 L 650 1044 "
                         "C 690 980 676 884 632 796 Z"})
    card.shape("boot-l", {"type": "path", "d": rrect_path(380, 1004, 118, 64, 26)})
    card.shape("boot-r", {"type": "path", "d": rrect_path(560, 1016, 120, 64, 26)})
    # The raised arm, waving back at the Visitor.
    card.shape("arm-r", {"type": "path", "d":
                         "M636 540 C 724 500 774 420 760 332 L 690 322 "
                         "C 702 400 664 468 596 506 Z"})
    card.shape("glove-r", {"type": "path", "d": ellipse_path(742, 310, 58, 58)})
    card.shape("arm-l", {"type": "path", "d":
                         "M384 552 C 312 596 286 672 312 744 L 384 724 "
                         "C 366 668 382 612 440 580 Z"})
    card.shape("glove-l", {"type": "path", "d": ellipse_path(306, 742, 52, 52)})
    # Helmet and visor.
    card.shape("helmet", {"type": "path", "d": ellipse_path(512, 352, 158, 162)})
    card.shape("visor", {"type": "path", "d": ellipse_path(512, 360, 118, 120)})


def flats(card):
    for sid, color in [("pack", SUIT_DK), ("leg-l", SUIT), ("leg-r", SUIT),
                       ("boot-l", SUIT_DK), ("boot-r", SUIT_DK), ("arm-l", SUIT),
                       ("arm-r", SUIT), ("torso", SUIT), ("belt", TRIM),
                       ("chest", SUIT_DK), ("glove-l", SUIT_DK),
                       ("glove-r", SUIT_DK), ("helmet", SUIT), ("visor", VISOR)]:
        card.fill("flats", shape=sid, color=color, expand=2)


def world(card):
    # The magenta world as a lit sphere behind the figure, with an atmosphere
    # rim. It sits on its own layer below the flats, so the suit covers it.
    card.node("world", {"type": "ellipse", "cx": 512, "cy": 1180, "rx": 572, "ry": 452,
                        "fill": "none",
                        "stroke": {"paint": "#ff9fe0aa", "width": 6}})
    card.node("world", {"type": "ellipse", "cx": 512, "cy": 1180, "rx": 558, "ry": 438,
                        "fill": radial(400, 1030, 620,
                                       [[0, "#ffd6f2"], [0.25, MAGENTA],
                                        [0.6, "#8a2f98"], [1, "#2a0f3a"]])})
    card.node("world", {"type": "ellipse", "cx": 512, "cy": 1180, "rx": 558, "ry": 438,
                        "fill": radial(760, 1360, 520,
                                       [[0, "#1a0626cc"], [0.6, "#2a0f3a44"],
                                        [1, "#2a0f3a00"]])})


def visor_reflection(card):
    # The gold visor: a reflective dome, the world's curve, and a tiny Visitor.
    card.node("visorfx", {"type": "ellipse", "cx": 512, "cy": 360, "rx": 118, "ry": 120,
                          "fill": radial(470, 316, 150,
                                         [[0, GOLD], [0.55, "#d98a2f"],
                                          [1, "#5a2f10"]])})
    # The world reflected as a curved band across the bottom of the visor,
    # leaving the gold to dominate the upper two thirds.
    card.node("visorfx", {"type": "ellipse", "cx": 512, "cy": 452, "rx": 108, "ry": 52,
                          "fill": radial(500, 452, 110,
                                         [[0, "#ff8fd8"], [0.6, "#b0407a"],
                                          [1, "#6a2f5a"]]),
                          "clip": ellipse_path(512, 360, 116, 118)})
    # The Visitor, waving, mirrored small in the gold: a tall head, deep eyes
    # and a raised arm, the pose it holds on card 03.
    card.node("visorfx", {"type": "ellipse", "cx": 500, "cy": 392, "rx": 20, "ry": 30,
                          "fill": "#2e4234"})
    card.node("visorfx", {"type": "ellipse", "cx": 500, "cy": 356, "rx": 19, "ry": 24,
                          "fill": "#3a5443"})
    card.node("visorfx", {"type": "ellipse", "cx": 494, "cy": 352, "rx": 4, "ry": 6,
                          "fill": "#0c140f"})
    card.node("visorfx", {"type": "ellipse", "cx": 508, "cy": 352, "rx": 4, "ry": 6,
                          "fill": "#0c140f"})
    card.node("visorfx", {"type": "path", "d": "M518 372 C 540 360 552 340 548 318",
                          "fill": "none",
                          "stroke": {"paint": "#3a5444", "width": 6, "cap": "round"}})
    # A bright catchlight and the mirror seam.
    card.node("light", {"type": "ellipse", "cx": 470, "cy": 312, "rx": 30, "ry": 20,
                        "fill": "#fff3cfdd"})
    card.node("visorfx", {"type": "ellipse", "cx": 512, "cy": 360, "rx": 118, "ry": 120,
                          "fill": "none",
                          "stroke": {"paint": "#fff0c8cc", "width": 3}})


def light(card):
    card.light(["pack", "torso", "leg-l", "leg-r", "arm-l", "arm-r"], depth=24,
               soft=2, rim_width=6, shade_color=SHADE, rim_color=RIM, strength=0.8)
    card.light(["helmet"], depth=34, soft=1, rim_width=8, shade_color="#2c3a56",
               rim_color="#ffffff", strength=0.65)
    card.light(["glove-l", "glove-r", "boot-l", "boot-r", "chest"], depth=14,
               soft=1, rim_width=4, shade_color=SHADE, rim_color=RIM, strength=0.9)


def tether(card):
    # The lifeline, curling off the pack to the edge, and a chest patch.
    card.node("tether", {"type": "path", "d":
                         "M372 560 C 250 620 180 740 150 900 C 132 1000 150 1120 220 1200",
                         "fill": "none",
                         "stroke": {"paint": "#ffd36b", "width": 7, "cap": "round"}})
    card.node("tether", {"type": "path", "d":
                         "M372 560 C 250 620 180 740 150 900 C 132 1000 150 1120 220 1200",
                         "fill": "none",
                         "stroke": {"paint": "#7a5a20", "width": 7, "cap": "round",
                                    "dash": [4, 22]}})
    card.node("patch", {"type": "ellipse", "cx": 512, "cy": 600, "rx": 38, "ry": 38,
                        "fill": CYAN + "22",
                        "stroke": {"paint": CYAN, "width": 3}})
    card.node("patch", {"type": "text", "text": "FC", "font": "Orbitron Bold",
                        "size": 30, "x": 512, "y": 614, "align": "center",
                        "tracking": 2, "fill": CYAN})


def glow(card):
    card.node("glow", {"type": "ellipse", "cx": 742, "cy": 310, "rx": 90, "ry": 90,
                       "fill": radial(742, 310, 90,
                                      [[0, CYAN + "66"], [1, CYAN + "00"]])})


def ink(card):
    card.ink(weight=9, seed=3, shapes=["torso", "pack", "leg-l", "leg-r"])
    card.ink(weight=8, seed=4, shapes=["arm-l", "arm-r"])
    card.ink(weight=7, seed=5, shapes=["helmet", "boot-l", "boot-r", "glove-l",
                                       "glove-r", "belt", "chest"])
    card.ink(weight=6, seed=6, shapes=["visor"])


def build():
    card = Card()
    for name, color in [("ink", INK), ("suit", SUIT), ("gold", GOLD),
                        ("trim", TRIM), ("glow", CYAN)]:
        card.palette(name, color)
    sky(card, ACCENT, horizon=0.52)
    card.layer("world", "vector")
    card.layer("tether", "vector")
    card.layer("sketch", "vector", visible=False)
    card.layer("flats", "paint")
    card.layer("shade", "paint", blend="multiply", opacity=0.82, clip=True)
    card.layer("rim", "paint", clip=True)
    card.layer("visorfx", "vector")
    card.layer("patch", "vector")
    card.layer("glow", "vector", blend="screen")
    card.layer("lines", "paint")
    card.layer("light", "vector", blend="add")
    shapes(card)
    flats(card)
    light(card)
    world(card)
    visor_reflection(card)
    tether(card)
    glow(card)
    ink(card)
    card_frame(card, "02 / FIRST CONTACT", "THE ASTRONAUT", ACCENT)
    card.dump()


if __name__ == "__main__":
    build()
