"""Card 02 - THE ASTRONAUT.

A spacewalker drifts on a tether, one glove raised. The gold visor reflects the
magenta world below and a small waving figure - the Visitor from card 03 -
so the middle card is the moment the two archetypes see each other.
"""

import sys

from kit import (CYAN, MAGENTA, Card, card_frame, ellipse_path,
                 radial, rrect_path, sky)

ACCENT = CYAN

LINE = "#1b2238"
SUIT = "#e8ebf2"
SUIT_DK = "#aeb6c8"
GOLD = "#ffcf6e"
TRIM = "#ff7a4d"


def shapes(card):
    # The planet the astronaut floats over, painted as a round form.
    card.shape("world", {"type": "path", "d": ellipse_path(512, 1180, 560, 440)})
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


def paint(card):
    # White suit painted with a warm key and a cool lavender shadow, so it
    # models without going grey, then relief-lit to show the oil body.
    card.paint_form("p-pack", ["pack"], SUIT_DK, weight=16, relief=(3.6, 3.2))
    card.paint_form("p-torso", ["torso"], SUIT, weight=20, relief=(4.4, 3.8))
    card.paint_form("p-legs", ["leg-l", "leg-r"], SUIT, weight=14,
                    form="cylinder", axis=80, relief=(3.8, 3.2))
    card.paint_form("p-boots", ["boot-l", "boot-r"], SUIT_DK, weight=9,
                    brush="oil-load", relief=(3.0, 2.6))
    card.paint_form("p-arm-l", ["arm-l"], SUIT, weight=13, form="cylinder",
                    axis=30, relief=(3.6, 3.2))
    card.paint_form("p-arm-r", ["arm-r"], SUIT, weight=13, form="cylinder",
                    axis=60, relief=(3.6, 3.2))
    card.paint_form("p-belt", ["belt"], TRIM, weight=9, brush="oil-load",
                    relief=(3.0, 2.4))
    card.paint_form("p-chest", ["chest"], SUIT_DK, weight=9, form="flat",
                    facing=[0.1, -0.2, 1], relief=(2.4, 2.2))
    card.paint_form("p-gloves", ["glove-l", "glove-r"], SUIT_DK, weight=9,
                    relief=(3.0, 2.6))
    card.paint_form("p-helmet", ["helmet"], SUIT, weight=18, relief=(4.2, 3.8))
    # The gold visor is painted as a round form so the reflection sits on oil,
    # not on a flat SVG radial.
    card.paint_form("p-visor", ["visor"], GOLD, weight=14, relief=(2.8, 3.0),
                    fillStrength=0.4)


def world(card):
    # The magenta world painted as a sphere, with a soft atmosphere rim above
    # the paint. The rim is vector; the sphere itself is oil.
    card.paint_form("p-world", ["world"], MAGENTA, weight=22, relief=(3.4, 4.0),
                    fillStrength=0.35)
    card.node("atmosphere", {"type": "ellipse", "cx": 512, "cy": 1180,
                             "rx": 572, "ry": 452, "fill": "none",
                             "stroke": {"paint": "#ff9fe0aa", "width": 6}})


def visor_reflection(card):
    # Reflection details over the painted gold: the world's curve, a tiny
    # Visitor waving, and a soft catchlight. Clip everything to the visor so
    # the paint's brushwork shows through around them.
    clip = ellipse_path(512, 360, 116, 118)
    card.node("visorfx", {"type": "ellipse", "cx": 512, "cy": 452, "rx": 108, "ry": 52,
                          "fill": radial(500, 452, 110,
                                         [[0, "#ff8fd8aa"], [0.6, "#b0407a88"],
                                          [1, "#6a2f5a00"]]),
                          "clip": clip})
    card.node("visorfx", {"type": "ellipse", "cx": 500, "cy": 392, "rx": 20, "ry": 30,
                          "fill": "#2e4234cc", "clip": clip})
    card.node("visorfx", {"type": "ellipse", "cx": 500, "cy": 356, "rx": 19, "ry": 24,
                          "fill": "#3a5443cc", "clip": clip})
    card.node("visorfx", {"type": "ellipse", "cx": 494, "cy": 352, "rx": 4, "ry": 6,
                          "fill": "#0c140f", "clip": clip})
    card.node("visorfx", {"type": "ellipse", "cx": 508, "cy": 352, "rx": 4, "ry": 6,
                          "fill": "#0c140f", "clip": clip})
    card.node("visorfx", {"type": "path", "d": "M518 372 C 540 360 552 340 548 318",
                          "fill": "none",
                          "stroke": {"paint": "#3a5444", "width": 6, "cap": "round"},
                          "clip": clip})
    card.node("light", {"type": "ellipse", "cx": 470, "cy": 312, "rx": 30, "ry": 20,
                        "fill": "#fff3cfdd", "clip": clip})


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


def build(card):
    for name, color in [("ink", LINE), ("suit", SUIT), ("gold", GOLD),
                        ("trim", TRIM), ("glow", CYAN)]:
        card.palette(name, color)
    sky(card, ACCENT, horizon=0.52)
    card.layer("atmosphere", "vector")
    card.layer("tether", "vector")
    card.layer("sketch", "vector", visible=False)
    shapes(card)
    world(card)
    paint(card)
    card.layer("lines", "paint", opacity=0.4)
    ink(card)
    card.brushwork()
    card.layer("visorfx", "vector")
    card.layer("patch", "vector")
    card.layer("glow", "vector", blend="screen")
    card.layer("light", "vector", blend="add")
    visor_reflection(card)
    tether(card)
    glow(card)
    card_frame(card, "02 / FIRST CONTACT", "THE ASTRONAUT", ACCENT)


if __name__ == "__main__":
    card = Card()
    build(card)
    if "--over" in sys.argv:
        card.dump_over(sizes=[36, 18, 9], threshold=8)
    else:
        card.dump()
