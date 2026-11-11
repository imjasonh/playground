"""Card 03 - THE VISITOR.

A tall, slender being with a high cranium, bioluminescent freckles and a glowing
collar frill. Its deep eyes mirror the astronaut's helmet, and a single raised
fingertip lights up - the gesture of first contact that the other two cards
answer.
"""

import math
import sys

from kit import (CYAN, MAGENTA, Card, _Rng, almond_path, card_frame,
                 limb_capsule, radial, sky)

ACCENT = MAGENTA

LINE = "#0e1626"
SKIN = "#5f8f8a"
SKIN_DK = "#2f5450"
ROBE = "#2a2550"
ROBE_LT = "#3b3570"
FRILL = "#8affd6"
GLINT = "#d8fff4"

VISITOR_NECK = (
    "M 488 548 C 468 558 462 612 468 648 "
    "C 472 668 492 678 512 680 "
    "C 532 678 552 668 556 648 "
    "C 562 612 556 558 536 548 "
    "C 524 544 500 544 488 548 Z")


def shapes(card):
    card.shape("head", {"type": "path", "d":
                        "M512 188 C 628 198 662 318 624 438 "
                        "C 598 518 552 568 512 578 "
                        "C 472 568 426 518 400 438 "
                        "C 362 318 396 198 512 188 Z"})
    card.shape("neck", {"type": "path", "d": VISITOR_NECK})
    card.shape("robe", {"type": "path", "d":
                        "M512 596 C 392 612 338 732 342 912 "
                        "C 346 1036 378 1148 418 1218 "
                        "L606 1218 C 646 1148 678 1036 682 912 "
                        "C 686 732 632 612 512 596 Z"})
    card.shape("collar", {"type": "path", "d":
                          "M512 578 C 602 578 658 634 658 692 "
                          "C 608 718 416 718 366 692 "
                          "C 366 634 422 578 512 578 Z"})
    card.shape("arm-r", {"type": "path", "d": limb_capsule(
        (598, 668), (668, 588), (704, 448), 34, 28, 22)})
    card.shape("hand-r", {"type": "path", "d":
                          "M 698 442 C 718 428 738 438 736 462 "
                          "C 732 486 712 498 692 488 "
                          "C 678 474 682 452 698 442 Z"})
    card.shape("finger", {"type": "path", "d":
                          "M 706 438 C 712 406 714 368 708 338 "
                          "L 722 336 C 728 368 728 408 722 440 Z"})
    card.shape("arm-l", {"type": "path", "d": limb_capsule(
        (426, 674), (348, 732), (312, 868), 32, 26, 24)})
    card.shape("hand-l", {"type": "path", "d":
                          "M 298 868 C 272 862 258 838 268 814 "
                          "C 282 792 318 788 334 808 "
                          "C 346 832 328 858 298 868 Z"})
    card.shape("eye-l", {"type": "path", "d": almond_path(468, 408, 44, 58, -6)})
    card.shape("eye-r", {"type": "path", "d": almond_path(556, 408, 44, 58, 6)})


def paint(card):
    card.paint_form("p-robe", ["robe"], ROBE, weight=20, relief=(4.0, 3.6))
    card.paint_form("p-arm-l", ["arm-l"], ROBE_LT, weight=13, form="cylinder",
                    axis=68, relief=(3.6, 3.2))
    card.paint_form("p-arm-r", ["arm-r"], ROBE_LT, weight=13, form="cylinder",
                    axis=52, relief=(3.6, 3.2))
    card.paint_form("p-neck", ["neck"], SKIN_DK, weight=9, form="cylinder",
                    axis=90, relief=(2.8, 2.6))
    card.paint_form("p-head", ["head"], SKIN, weight=16, relief=(4.2, 3.6))
    card.paint_form("p-collar", ["collar"], ROBE_LT, weight=10,
                    brush="oil-load", relief=(3.0, 2.6))
    card.paint_form("p-hands", ["hand-l", "hand-r", "finger"], SKIN, weight=8,
                    relief=(3.0, 2.4))
    card.paint_form("p-eyes", ["eye-l", "eye-r"], "#070d14", weight=7,
                    relief=None)


def eyes(card):
    for cx, tilt in ((468, -6), (556, 6)):
        clip = almond_path(cx, 408, 44, 58, tilt)
        card.node("inlay", {"type": "path", "d": clip,
                            "fill": radial(cx - 10, 392, 58,
                                           [[0, "#2a4a6a"], [0.55, "#101c30"],
                                            [1, "#05080e"]])})
        card.node("inlay", {"type": "ellipse", "cx": cx, "cy": 418, "rx": 16, "ry": 22,
                            "fill": "#02040a", "clip": clip})
        card.node("light", {"type": "ellipse", "cx": cx - 12, "cy": 388, "rx": 9,
                            "ry": 13, "fill": GLINT + "ee"})
        card.node("light", {"type": "ellipse", "cx": cx + 8, "cy": 422, "rx": 4,
                            "ry": 5, "fill": "#ffffffcc"})
        # Helmet glint in the pupil - looking back at card 02.
        card.node("light", {"type": "ellipse", "cx": cx - 4, "cy": 412, "rx": 6,
                            "ry": 8, "fill": "#c8e8ff88"})


def freckles(card):
    rng = _Rng(41)
    for _ in range(46):
        a = rng.next() * 2 * math.pi
        rad = 40 + rng.next() * 150
        x = 512 + math.cos(a) * rad * 0.7
        y = 360 + math.sin(a) * rad
        if y < 230 or y > 540:
            continue
        r = 1.6 + rng.next() * 3.4
        card.node("glow", {"type": "ellipse", "cx": x, "cy": y, "rx": r, "ry": r,
                           "fill": radial(x, y, r * 2.2,
                                          [[0, FRILL + "ee"], [0.5, CYAN + "66"],
                                           [1, CYAN + "00"]])})


def collar_glow(card):
    card.node("glow", {"type": "path", "d":
                       "M512 578 C 602 578 658 634 658 692 "
                       "C 608 718 416 718 366 692 "
                       "C 366 634 422 578 512 578 Z",
                       "fill": radial(512, 660, 150,
                                      [[0, FRILL + "aa"], [0.6, FRILL + "33"],
                                       [1, FRILL + "00"]]),
                       "blur": 6})
    for i in range(7):
        t = i / 6
        x = 400 + t * 224
        card.node("glow", {"type": "path",
                           "d": f"M{x:.0f} 692 C {x:.0f} 648 "
                                f"{512 + (x - 512) * 0.4:.0f} 608 512 596",
                           "fill": "none",
                           "stroke": {"paint": FRILL + "88", "width": 2.5}})


def fingertip(card):
    card.node("glow", {"type": "ellipse", "cx": 718, "cy": 336, "rx": 60, "ry": 60,
                       "fill": radial(718, 336, 60,
                                      [[0, "#ffffffcc"], [0.3, FRILL + "aa"],
                                       [0.7, CYAN + "44"], [1, CYAN + "00"]])})
    card.node("light", {"type": "ellipse", "cx": 718, "cy": 336, "rx": 12, "ry": 14,
                        "fill": "#ffffffff"})
    for dx, dy, r in [(28, -18, 3), (-22, -30, 2.4), (40, 16, 2.2), (14, -44, 2)]:
        card.node("glow", {"type": "ellipse", "cx": 718 + dx, "cy": 336 + dy,
                           "rx": r, "ry": r,
                           "fill": radial(718 + dx, 336 + dy, r * 2,
                                          [[0, GLINT], [1, CYAN + "00"]])})


def ink(card):
    card.ink(weight=7, seed=3, shapes=["robe"], wobble=1.8)
    card.ink(weight=6, seed=4, shapes=["arm-l", "arm-r", "head", "neck"],
             wobble=1.6)
    card.ink(weight=5, seed=5, shapes=["collar", "hand-l", "hand-r", "finger"],
             wobble=1.4)
    # Eyes: rim only, not a heavy outline.
    card.ink(weight=3, seed=6, shapes=["eye-l", "eye-r"], wobble=1.0)


def build(card):
    for name, color in [("ink", LINE), ("skin", SKIN), ("robe", ROBE),
                        ("frill", FRILL), ("glow", CYAN)]:
        card.palette(name, color)
    sky(card, ACCENT, horizon=0.44)
    card.layer("shadow", "vector", blend="multiply")
    card.node("shadow", {"type": "ellipse", "cx": 512, "cy": 1198, "rx": 220,
                         "ry": 32, "fill": "#120818aa", "blur": 14})
    card.layer("sketch", "vector", visible=False)
    shapes(card)
    paint(card)
    card.layer("lines", "paint", opacity=0.36)
    ink(card)
    card.brushwork()
    card.layer("inlay", "vector")
    card.layer("glow", "vector", blend="screen")
    card.layer("light", "vector", blend="add")
    eyes(card)
    freckles(card)
    collar_glow(card)
    fingertip(card)
    card_frame(card, "03 / FIRST CONTACT", "THE VISITOR", ACCENT)


if __name__ == "__main__":
    card = Card()
    build(card)
    if "--over" in sys.argv:
        card.dump_over(sizes=[32, 16, 8], threshold=6, brush="oil-load")
    else:
        card.dump()
