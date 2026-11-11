"""Card 02 - THE ASTRONAUT.

A spacewalker drifts on a tether, one glove raised. The gold visor reflects the
magenta world below and a small waving figure - the Visitor from card 03 -
so the middle card is the moment the two archetypes see each other.
"""

import sys

from kit import (CYAN, MAGENTA, Card, card_frame, ellipse_path,
                 limb_capsule, radial, sky)

ACCENT = CYAN

LINE = "#1b2238"
SUIT = "#e8ebf2"
SUIT_DK = "#aeb6c8"
GOLD = "#ffcf6e"
TRIM = "#ff7a4d"

ASTRONAUT_PACK = (
    "M 378 468 C 348 512 356 608 388 688 L 432 672 "
    "C 418 598 412 528 438 476 Z")
ASTRONAUT_TORSO = (
    "M 388 502 C 368 548 364 648 382 744 L 398 812 "
    "C 412 842 446 858 512 860 C 578 858 612 842 626 812 "
    "L 642 744 C 660 648 656 548 636 502 "
    "C 608 478 548 468 512 468 C 476 468 416 478 388 502 Z")
ASTRONAUT_HELMET = (
    "M 368 388 C 392 288 448 248 512 244 C 576 248 632 288 656 388 "
    "C 632 412 576 428 512 432 C 448 428 392 412 368 388 Z")
ASTRONAUT_VISOR = (
    "M 402 368 C 428 312 496 288 512 286 C 528 288 596 312 622 368 "
    "C 596 408 528 424 512 426 C 496 424 428 408 402 368 Z")
ASTRONAUT_BOOT_L = (
    "M 382 988 C 364 1020 376 1056 418 1072 L 478 1066 "
    "C 492 1048 488 1012 468 984 Z")
ASTRONAUT_BOOT_R = (
    "M 562 984 C 542 1012 538 1048 552 1066 L 612 1072 "
    "C 654 1056 666 1020 648 988 Z")


def shapes(card):
    card.shape("world", {"type": "path", "d": ellipse_path(512, 1180, 560, 440)})
    card.shape("pack", {"type": "path", "d": ASTRONAUT_PACK})
    card.shape("torso", {"type": "path", "d": ASTRONAUT_TORSO})
    card.shape("belt", {"type": "path", "d":
                        "M 372 748 C 380 724 408 712 512 710 "
                        "C 616 712 644 724 652 748 "
                        "L 648 782 L 376 782 Z"})
    card.shape("chest", {"type": "path", "d":
                         "M 454 548 C 446 538 446 624 456 634 "
                         "L 568 628 C 578 618 578 532 568 542 Z"})
    card.shape("leg-l", {"type": "path", "d": limb_capsule(
        (418, 812), (398, 902), (422, 988), 52, 46, 44)})
    card.shape("leg-r", {"type": "path", "d": limb_capsule(
        (606, 812), (626, 902), (602, 988), 52, 46, 44)})
    card.shape("boot-l", {"type": "path", "d": ASTRONAUT_BOOT_L})
    card.shape("boot-r", {"type": "path", "d": ASTRONAUT_BOOT_R})
    card.shape("arm-r", {"type": "path", "d": limb_capsule(
        (588, 548), (668, 468), (736, 318), 42, 36, 48)})
    card.shape("glove-r", {"type": "path", "d":
                           "M 722 298 C 748 288 768 306 764 332 "
                           "C 758 362 728 378 702 368 "
                           "C 686 352 692 316 722 298 Z"})
    card.shape("arm-l", {"type": "path", "d": limb_capsule(
        (432, 560), (352, 620), (298, 728), 40, 34, 42)})
    card.shape("glove-l", {"type": "path", "d":
                           "M 278 712 C 252 702 244 678 258 656 "
                           "C 276 638 312 642 328 662 "
                           "C 338 688 318 714 278 712 Z"})
    card.shape("helmet", {"type": "path", "d": ASTRONAUT_HELMET})
    card.shape("visor", {"type": "path", "d": ASTRONAUT_VISOR})


def paint(card):
    card.paint_form("p-pack", ["pack"], SUIT_DK, weight=16, relief=(3.6, 3.2))
    card.paint_form("p-torso", ["torso"], SUIT, weight=22, relief=(4.6, 3.8))
    card.paint_form("p-legs", ["leg-l", "leg-r"], SUIT, weight=15,
                    form="cylinder", axis=82, relief=(3.8, 3.2))
    card.paint_form("p-boots", ["boot-l", "boot-r"], SUIT_DK, weight=10,
                    brush="oil-load", relief=(3.0, 2.6))
    card.paint_form("p-arm-l", ["arm-l"], SUIT, weight=14, form="cylinder",
                    axis=28, relief=(3.6, 3.2))
    card.paint_form("p-arm-r", ["arm-r"], SUIT, weight=14, form="cylinder",
                    axis=58, relief=(3.6, 3.2))
    card.paint_form("p-gloves", ["glove-l", "glove-r"], SUIT_DK, weight=10,
                    relief=(3.2, 2.6))
    card.paint_form("p-belt", ["belt"], TRIM, weight=9, brush="oil-load",
                    relief=(3.0, 2.4))
    card.paint_form("p-chest", ["chest"], SUIT_DK, weight=9, form="flat",
                    facing=[0.1, -0.2, 1], relief=(2.4, 2.2))
    card.paint_form("p-helmet", ["helmet"], SUIT, weight=19, relief=(4.2, 3.8))
    card.paint_form("p-visor", ["visor"], GOLD, weight=15, relief=(2.8, 3.0),
                    fillStrength=0.42)


def world(card):
    card.paint_form("p-world", ["world"], MAGENTA, weight=24, relief=(3.4, 4.0),
                    fillStrength=0.35)
    card.node("atmosphere", {"type": "ellipse", "cx": 512, "cy": 1180,
                             "rx": 572, "ry": 452, "fill": "none",
                             "stroke": {"paint": "#ff9fe0aa", "width": 6}})


def visor_reflection(card):
    clip = ASTRONAUT_VISOR
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
    card.node("tether", {"type": "path", "d":
                         "M368 548 C 248 612 168 736 142 908 "
                         "C 128 1008 148 1124 218 1196",
                         "fill": "none",
                         "stroke": {"paint": "#ffd36b", "width": 7, "cap": "round"}})
    card.node("tether", {"type": "path", "d":
                         "M368 548 C 248 612 168 736 142 908 "
                         "C 128 1008 148 1124 218 1196",
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
    card.node("glow", {"type": "ellipse", "cx": 736, "cy": 318, "rx": 90, "ry": 90,
                       "fill": radial(736, 318, 90,
                                      [[0, CYAN + "66"], [1, CYAN + "00"]])})


def ink(card):
    card.ink(weight=7, seed=3, shapes=["torso", "pack", "leg-l", "leg-r"],
             wobble=1.8)
    card.ink(weight=6, seed=4, shapes=["arm-l", "arm-r"], wobble=1.8)
    card.ink(weight=5, seed=5, shapes=["helmet", "boot-l", "boot-r", "glove-l",
                                       "glove-r", "belt", "chest"], wobble=1.6)
    card.ink(weight=4, seed=6, shapes=["visor"], wobble=1.2)


def build(card):
    for name, color in [("ink", LINE), ("suit", SUIT), ("gold", GOLD),
                        ("trim", TRIM), ("glow", CYAN)]:
        card.palette(name, color)
    sky(card, ACCENT, horizon=0.52)
    card.layer("shadow", "vector", blend="multiply")
    card.node("shadow", {"type": "ellipse", "cx": 512, "cy": 1088, "rx": 180,
                         "ry": 26, "fill": "#0c1020aa", "blur": 12})
    card.layer("atmosphere", "vector")
    card.layer("tether", "vector")
    card.layer("sketch", "vector", visible=False)
    shapes(card)
    world(card)
    paint(card)
    card.layer("lines", "paint", opacity=0.35)
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
        card.dump_over(sizes=[32, 16, 8], threshold=6, brush="oil-load")
    else:
        card.dump()
