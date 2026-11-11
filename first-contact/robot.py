"""Card 01 - THE ROBOT.

A rusty caretaker robot cradles a glowing sprout under a glass bell jar. Its
dome is a vacuum-tube head; a chest porthole shows the same magenta world the
astronaut floats over on card 02, so the three cards share one sky.
"""

import sys

from kit import (AMBER, CYAN, MAGENTA, Card, card_frame, ellipse_path,
                 linear, radial, rrect_path, sky)

ACCENT = AMBER

LINE = "#2a1712"
RUST = "#b9633b"
RUST_DK = "#843f26"
STEEL = "#8b94a8"
STEEL_DK = "#454c5e"
GLASS = "#bfe9ff"
LEAF = "#8ef06f"


def shapes(card):
    card.shape("torso", {"type": "path", "d": rrect_path(316, 612, 392, 430, 76)})
    card.shape("panel", {"type": "path", "d": rrect_path(400, 688, 224, 158, 30)})
    card.shape("port", {"type": "path", "d": ellipse_path(512, 752, 58, 58)})
    card.shape("hip", {"type": "path", "d": rrect_path(338, 1000, 348, 92, 44)})
    card.shape("neck", {"type": "path", "d": rrect_path(470, 548, 84, 86, 24)})
    card.shape("head", {"type": "path", "d": rrect_path(344, 356, 336, 236, 110)})
    card.shape("dome", {"type": "path", "d": ellipse_path(512, 352, 112, 92)})
    card.shape("eye", {"type": "path", "d": ellipse_path(512, 474, 104, 78)})
    card.shape("ear-l", {"type": "path", "d": rrect_path(312, 430, 44, 96, 20)})
    card.shape("ear-r", {"type": "path", "d": rrect_path(668, 430, 44, 96, 20)})
    card.shape("arm-l", {"type": "path", "d":
                         "M352 700 C 300 782 300 880 372 930 L 436 892 "
                         "C 386 858 384 792 420 736 Z"})
    card.shape("arm-r", {"type": "path", "d":
                         "M672 700 C 724 782 724 880 652 930 L 588 892 "
                         "C 638 858 640 792 604 736 Z"})
    # The bell jar: a glass dome on a little plinth, drawn over the arms.
    card.shape("jar", {"type": "path", "d":
                       "M430 940 C 430 820 594 820 594 940 Z"})
    card.shape("jar-base", {"type": "path", "d": rrect_path(418, 936, 188, 26, 10)})
    card.shape("stem", {"type": "path", "d":
                        "M510 936 C 506 904 508 876 516 854 L 524 856 "
                        "C 518 880 518 908 522 936 Z"})
    card.shape("leaf-l", {"type": "path", "d":
                          "M514 884 C 470 876 452 848 470 824 C 500 836 516 858 514 884 Z"})
    card.shape("leaf-r", {"type": "path", "d":
                          "M520 870 C 560 858 580 828 566 802 C 532 818 520 844 520 870 Z"})


def paint(card):
    # Each form is painted on its own layer, back to front, with oil strokes
    # that follow the form and a relief effect that lights the paint body.
    card.paint_form("p-hip", ["hip"], RUST_DK, weight=18, relief=(4.0, 3.6))
    card.paint_form("p-torso", ["torso"], RUST, weight=21, relief=(4.6, 3.8))
    card.paint_form("p-arms", ["arm-l", "arm-r"], RUST, weight=13,
                    relief=(3.8, 3.2))
    card.paint_form("p-neck", ["neck"], STEEL_DK, weight=9, form="cylinder",
                    axis=90, relief=(3.0, 2.6))
    card.paint_form("p-head", ["head"], RUST, weight=16, relief=(4.3, 3.6))
    card.paint_form("p-ears", ["ear-l", "ear-r"], STEEL, weight=8,
                    brush="oil-load", relief=(3.0, 2.6))
    card.paint_form("p-panel", ["panel"], STEEL_DK, weight=11, form="flat",
                    facing=[0.1, -0.2, 1], brush="oil-load", relief=(2.6, 2.4))
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
    # The porthole world sits above the shading so it reads as emissive glass.
    card.node("inlay", {"type": "ellipse", "cx": 512, "cy": 752, "rx": 54, "ry": 54,
                        "fill": radial(500, 742, 58,
                                       [[0, "#ffd0f0"], [0.3, MAGENTA],
                                        [0.7, "#7a2f8c"], [1, "#2a0f3a"]])})
    card.node("inlay", {"type": "ellipse", "cx": 512, "cy": 752, "rx": 54, "ry": 54,
                        "fill": "none",
                        "stroke": {"paint": "#dff6ffaa", "width": 3}})
    # A friendly amber iris and pupil in the big eye lens.
    card.node("inlay", {"type": "ellipse", "cx": 512, "cy": 476, "rx": 56, "ry": 44,
                        "fill": radial(500, 462, 60,
                                       [[0, "#ffe3a8"], [0.5, AMBER],
                                        [1, "#b85a26"]])})
    card.node("inlay", {"type": "ellipse", "cx": 512, "cy": 482, "rx": 22, "ry": 20,
                        "fill": "#1a0e08"})


def glow(card):
    # The sprout's halo on a screen layer, with a bright core.
    card.node("glow", {"type": "ellipse", "cx": 512, "cy": 876, "rx": 150, "ry": 170,
                       "fill": radial(512, 876, 170,
                                      [[0, CYAN + "88"], [0.5, "#4fd0a033"],
                                       [1, "#2a6f8800"]])})
    card.node("light", {"type": "ellipse", "cx": 512, "cy": 872, "rx": 54, "ry": 60,
                        "fill": radial(512, 866, 60,
                                       [[0, "#f2fff4ff"], [0.5, "#bff0d088"],
                                        [1, "#6fd0a000"]])})
    # The eye's inner glow and catchlight.
    card.node("glow", {"type": "ellipse", "cx": 512, "cy": 474, "rx": 70, "ry": 54,
                       "fill": radial(512, 474, 70,
                                      [[0, AMBER + "cc"], [0.5, "#d06a2f66"],
                                       [1, "#d06a2f00"]])})


def details(card):
    card.node("light", {"type": "ellipse", "cx": 486, "cy": 456, "rx": 15, "ry": 11,
                        "fill": "#fff4d8ee"})
    # A glass bell jar over the sprout: a soft translucent dome and highlight.
    card.node("jarglass", {"type": "path", "d":
                           "M430 940 C 430 820 594 820 594 940 Z",
                           "fill": linear(430, 820, 594, 940,
                                          [[0, "#bfe9ff22"], [0.5, "#bfe9ff11"],
                                           [1, "#bfe9ff33"]]),
                           "stroke": {"paint": "#dff6ff99", "width": 3},
                           "blur": 1.5})
    card.node("jarglass", {"type": "path", "d":
                           "M452 930 C 452 850 486 824 512 822",
                           "fill": "none",
                           "stroke": {"paint": "#ffffff66", "width": 6},
                           "blur": 2})
    # A little antenna bulb on the dome.
    card.ink(weight=5, seed=30, path="M512 262 L512 214")
    card.node("glow", {"type": "ellipse", "cx": 512, "cy": 204, "rx": 16, "ry": 16,
                       "fill": radial(512, 204, 16,
                                      [[0, "#fff6b0ff"], [1, "#ffb76500"]])})


def ink(card):
    card.ink(weight=9, seed=3, shapes=["head", "neck", "torso", "hip"])
    card.ink(weight=8, seed=4, shapes=["arm-l", "arm-r"])
    card.ink(weight=7, seed=5, shapes=["dome", "eye", "ear-l", "ear-r"])
    card.ink(weight=6, seed=6, shapes=["panel", "port"])
    card.ink(weight=5, seed=8, shapes=["jar-base", "stem", "leaf-l", "leaf-r"])
    # Face seam and a friendly lower eyelid, drawn as open paths.
    card.ink(weight=4, seed=9, path="M470 474 C 500 500 524 500 554 474")
    # Tally marks on the hip, a caretaker counting the days.
    for i, x in enumerate((372, 392, 412, 432)):
        card.ink(weight=3, seed=20 + i, path=f"M{x} 1026 L{x} 1066")
    card.ink(weight=3, seed=25, path="M366 1058 L440 1034")


def build(card):
    for name, color in [("ink", LINE), ("rust", RUST), ("steel", STEEL),
                        ("leaf", LEAF), ("glow", CYAN)]:
        card.palette(name, color)
    sky(card, ACCENT)
    card.layer("sketch", "vector", visible=False)
    shapes(card)
    paint(card)
    # Soft sketch lines under the brushwork, so the paint-over softens them.
    card.layer("lines", "paint", opacity=0.45)
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
        card.dump_over(sizes=[36, 18, 9], threshold=8)
    else:
        card.dump()
