"""Card 01 - THE ROBOT.

A rusty caretaker robot cradles a glowing sprout under a glass bell jar. Its
dome is a vacuum-tube head; a chest porthole shows the same magenta world the
astronaut floats over on card 02, so the three cards share one sky.
"""

import sys

from kit import (AMBER, CYAN, MAGENTA, Card, card_frame,
                 linear, limb_capsule, radial, sky)

ACCENT = AMBER

LINE = "#2a1712"
RUST = "#b9633b"
RUST_DK = "#843f26"
STEEL = "#8b94a8"
STEEL_DK = "#454c5e"
GLASS = "#bfe9ff"
LEAF = "#8ef06f"

# Hand-drawn hull paths: a dented boiler torso, a facet-jointed head, and skid
# feet that flare at the track lip instead of rounded rectangles.
ROBOT_TORSO = (
    "M 362 628 C 334 592 348 548 402 532 L 618 528 "
    "C 684 534 714 580 706 642 C 698 712 672 778 626 818 "
    "L 418 812 C 368 802 342 748 352 692 Z")
ROBOT_HEAD = (
    "M 396 552 C 368 492 392 372 468 348 C 532 328 596 342 642 388 "
    "C 686 444 674 518 628 558 C 572 578 466 574 418 562 "
    "C 398 560 390 566 396 552 Z")
ROBOT_HIP = (
    "M 352 998 C 338 1034 378 1076 452 1088 L 578 1084 "
    "C 648 1070 682 1030 668 990 L 638 962 L 392 968 Z")
ROBOT_NECK = (
    "M 478 542 C 468 532 468 618 478 628 L 546 624 "
    "C 556 614 556 528 546 538 Z")
ROBOT_PANEL = (
    "M 428 682 C 422 672 424 758 432 768 L 592 762 "
    "C 602 752 598 666 588 676 Z")
ROBOT_DOME = (
    "M 412 348 C 448 294 576 294 612 348 C 592 318 448 318 412 348 Z")


def shapes(card):
    card.shape("torso", {"type": "path", "d": ROBOT_TORSO})
    card.shape("head", {"type": "path", "d": ROBOT_HEAD})
    card.shape("hip", {"type": "path", "d": ROBOT_HIP})
    card.shape("neck", {"type": "path", "d": ROBOT_NECK})
    card.shape("panel", {"type": "path", "d": ROBOT_PANEL})
    card.shape("port", {"type": "path", "d":
                         "M 512 748 C 546 748 572 774 572 808 "
                         "C 572 842 546 868 512 868 "
                         "C 478 868 452 842 452 808 C 452 774 478 748 512 748 Z"})
    card.shape("dome", {"type": "path", "d": ROBOT_DOME})
    card.shape("eye", {"type": "path", "d":
                       "M 428 478 C 466 432 558 432 596 478 "
                       "C 558 518 466 518 428 478 Z"})
    card.shape("ear-l", {"type": "path", "d":
                           "M 318 456 C 298 468 302 524 324 536 "
                           "C 344 522 342 468 318 456 Z"})
    card.shape("ear-r", {"type": "path", "d":
                           "M 706 456 C 726 468 722 524 700 536 "
                           "C 680 522 682 468 706 456 Z"})
    card.shape("arm-l", {"type": "path", "d": limb_capsule(
        (362, 668), (318, 758), (388, 912), 46, 38, 52)})
    card.shape("arm-r", {"type": "path", "d": limb_capsule(
        (662, 668), (706, 758), (636, 912), 46, 38, 52)})
    card.shape("jar", {"type": "path", "d":
                       "M 438 948 C 428 824 486 802 512 798 "
                       "C 538 802 596 824 586 948 Z"})
    card.shape("jar-base", {"type": "path", "d":
                            "M 408 944 C 408 928 420 916 438 912 "
                            "L 586 912 C 604 916 616 928 616 944 "
                            "L 616 960 L 408 960 Z"})
    card.shape("stem", {"type": "path", "d":
                        "M 508 944 C 502 908 504 874 514 848 "
                        "L 528 850 C 520 878 520 912 526 944 Z"})
    card.shape("leaf-l", {"type": "path", "d":
                          "M 508 892 C 458 878 432 842 456 812 "
                          "C 492 828 508 858 508 892 Z"})
    card.shape("leaf-r", {"type": "path", "d":
                          "M 518 876 C 562 858 588 824 568 796 "
                          "C 528 814 518 844 518 876 Z"})


def paint(card):
    card.paint_form("p-hip", ["hip"], RUST_DK, weight=18, relief=(4.0, 3.6))
    card.paint_form("p-torso", ["torso"], RUST, weight=22, relief=(4.8, 3.8))
    card.paint_form("p-arms", ["arm-l", "arm-r"], RUST, weight=14,
                    relief=(3.8, 3.2))
    card.paint_form("p-neck", ["neck"], STEEL_DK, weight=9, form="cylinder",
                    axis=88, relief=(3.0, 2.6))
    card.paint_form("p-head", ["head"], RUST, weight=17, relief=(4.3, 3.6))
    card.paint_form("p-ears", ["ear-l", "ear-r"], STEEL, weight=8,
                    brush="oil-load", relief=(3.0, 2.6))
    card.paint_form("p-panel", ["panel"], STEEL_DK, weight=11, form="flat",
                    facing=[0.12, -0.25, 1], brush="oil-load", relief=(2.6, 2.4))
    card.hatch("p-panel", ["panel"], angle=24, spacing=22, length=[6, 12],
               weight=2, color="#241f38", opacity=0.35, seed=7)
    card.paint_form("p-dome", ["dome"], GLASS, weight=12, fillStrength=0.5,
                    relief=(1.4, 3.0))
    card.paint_form("p-eye", ["eye"], "#12223c", weight=9, relief=(1.2, 2.6))
    card.paint_form("p-port", ["port"], "#160a26", weight=6, relief=None)
    card.paint_form("p-jarbase", ["jar-base"], STEEL_DK, weight=7,
                    brush="oil-load", relief=(2.2, 2.2))
    card.paint_form("p-sprout", ["stem"], "#5fb84a", weight=6, relief=(2.4, 2.0))
    card.paint_form("p-leaves", ["leaf-l", "leaf-r"], LEAF, weight=7,
                    relief=(2.8, 2.2))


def inlay(card):
    card.node("inlay", {"type": "ellipse", "cx": 512, "cy": 808, "rx": 54, "ry": 54,
                        "fill": radial(500, 796, 58,
                                       [[0, "#ffd0f0"], [0.3, MAGENTA],
                                        [0.7, "#7a2f8c"], [1, "#2a0f3a"]])})
    card.node("inlay", {"type": "ellipse", "cx": 512, "cy": 808, "rx": 54, "ry": 54,
                        "fill": "none",
                        "stroke": {"paint": "#dff6ffaa", "width": 3}})
    card.node("inlay", {"type": "ellipse", "cx": 512, "cy": 478, "rx": 52, "ry": 40,
                        "fill": radial(500, 462, 60,
                                       [[0, "#ffe3a8"], [0.5, AMBER],
                                        [1, "#b85a26"]])})
    card.node("inlay", {"type": "ellipse", "cx": 512, "cy": 484, "rx": 20, "ry": 18,
                        "fill": "#1a0e08"})


def glow(card):
    card.node("glow", {"type": "ellipse", "cx": 512, "cy": 878, "rx": 150, "ry": 170,
                       "fill": radial(512, 878, 170,
                                      [[0, CYAN + "88"], [0.5, "#4fd0a033"],
                                       [1, "#2a6f8800"]])})
    card.node("light", {"type": "ellipse", "cx": 512, "cy": 874, "rx": 54, "ry": 60,
                        "fill": radial(512, 868, 60,
                                       [[0, "#f2fff4ff"], [0.5, "#bff0d088"],
                                        [1, "#6fd0a000"]])})
    card.node("glow", {"type": "ellipse", "cx": 512, "cy": 476, "rx": 68, "ry": 52,
                       "fill": radial(512, 476, 70,
                                      [[0, AMBER + "cc"], [0.5, "#d06a2f66"],
                                       [1, "#d06a2f00"]])})


def details(card):
    card.node("light", {"type": "ellipse", "cx": 486, "cy": 458, "rx": 15, "ry": 11,
                        "fill": "#fff4d8ee"})
    card.node("jarglass", {"type": "path", "d":
                           "M 438 948 C 428 824 486 802 512 798 "
                           "C 538 802 596 824 586 948 Z",
                           "fill": linear(430, 820, 594, 940,
                                          [[0, "#bfe9ff22"], [0.5, "#bfe9ff11"],
                                           [1, "#bfe9ff33"]]),
                           "stroke": {"paint": "#dff6ff99", "width": 3},
                           "blur": 1.5})
    card.node("jarglass", {"type": "path", "d":
                           "M 452 930 C 452 850 486 824 512 822",
                           "fill": "none",
                           "stroke": {"paint": "#ffffff66", "width": 6},
                           "blur": 2})
    card.ink(weight=5, seed=30, path="M512 262 L512 214")
    card.node("glow", {"type": "ellipse", "cx": 512, "cy": 204, "rx": 16, "ry": 16,
                       "fill": radial(512, 204, 16,
                                      [[0, "#fff6b0ff"], [1, "#ffb76500"]])})


def ink(card):
    card.ink(weight=8, seed=3, shapes=["head", "neck", "torso", "hip"])
    card.ink(weight=7, seed=4, shapes=["arm-l", "arm-r"])
    card.ink(weight=6, seed=5, shapes=["dome", "eye", "ear-l", "ear-r"])
    card.ink(weight=5, seed=6, shapes=["panel", "port"])
    card.ink(weight=4, seed=8, shapes=["jar-base", "stem", "leaf-l", "leaf-r"])
    card.ink(weight=3, seed=9, path="M468 478 C 500 502 524 502 556 478")
    for i, x in enumerate((372, 392, 412, 432)):
        card.ink(weight=3, seed=20 + i, path=f"M{x} 1026 L{x} 1066")
    card.ink(weight=3, seed=25, path="M366 1058 L440 1034")


def build(card):
    for name, color in [("ink", LINE), ("rust", RUST), ("steel", STEEL),
                        ("leaf", LEAF), ("glow", CYAN)]:
        card.palette(name, color)
    sky(card, ACCENT)
    card.layer("shadow", "vector", blend="multiply")
    card.node("shadow", {"type": "ellipse", "cx": 512, "cy": 1068, "rx": 200,
                         "ry": 28, "fill": "#1a0f28aa", "blur": 12})
    card.layer("sketch", "vector", visible=False)
    shapes(card)
    paint(card)
    card.layer("lines", "paint", opacity=0.38)
    ink(card)
    card.brushwork()
    card.layer("inlay", "vector")
    card.layer("glow", "vector", blend="screen")
    card.layer("jarglass", "vector")
    card.layer("light", "vector", blend="add")
    inlay(card)
    glow(card)
    details(card)
    card_frame(card, "01 / FIRST CONTACT", "THE ROBOT", ACCENT)


if __name__ == "__main__":
    card = Card()
    build(card)
    if "--over" in sys.argv:
        card.dump_over(sizes=[32, 16, 8], threshold=6, brush="oil-load")
    else:
        card.dump()
