"""Card 03 - THE VISITOR.

A tall, slender being with a high cranium, bioluminescent freckles and a glowing
collar frill. Its deep eyes mirror the astronaut's helmet, and a single raised
fingertip lights up - the gesture of first contact that the other two cards
answer.
"""

import math

from kit import (CYAN, INK, MAGENTA, Card, _Rng, card_frame, ellipse_path,
                 linear, radial, rrect_path, sky)

ACCENT = MAGENTA

SKIN = "#5f8f8a"
SKIN_DK = "#2f5450"
ROBE = "#2a2550"
ROBE_LT = "#3b3570"
FRILL = "#8affd6"
SHADE = "#17243a"
RIM = "#b8ffe9"
GLINT = "#d8fff4"


def shapes(card):
    # A tall cranium tapering to a narrow chin.
    card.shape("head", {"type": "path", "d":
                        "M512 196 C 620 206 648 320 616 430 C 596 500 556 548 512 556 "
                        "C 468 548 428 500 408 430 C 376 320 404 206 512 196 Z"})
    card.shape("neck", {"type": "path", "d": rrect_path(474, 540, 76, 96, 30)})
    # A long robed body.
    card.shape("robe", {"type": "path", "d":
                        "M512 600 C 404 612 356 720 360 900 C 362 1020 388 1120 420 1200 "
                        "L604 1200 C 636 1120 662 1020 664 900 C 668 720 620 612 512 600 Z"})
    card.shape("collar", {"type": "path", "d":
                          "M512 584 C 596 584 648 636 648 688 C 600 712 424 712 376 688 "
                          "C 376 636 428 584 512 584 Z"})
    # Long arms, one raised with a pointing hand.
    card.shape("arm-r", {"type": "path", "d":
                         "M596 672 C 664 628 700 540 694 436 L 724 430 "
                         "C 746 536 716 648 640 712 Z"})
    card.shape("hand-r", {"type": "path", "d":
                          "M706 430 C 724 420 736 430 734 448 C 730 470 716 478 700 472 "
                          "C 690 462 694 440 706 430 Z"})
    card.shape("finger", {"type": "path", "d":
                          "M712 432 C 716 404 716 372 712 348 L 724 346 "
                          "C 730 372 730 406 726 434 Z"})
    card.shape("arm-l", {"type": "path", "d":
                         "M430 676 C 372 720 344 800 352 880 L 384 876 "
                         "C 380 806 404 740 456 704 Z"})
    card.shape("hand-l", {"type": "path", "d": ellipse_path(366, 892, 30, 38)})
    # The large, deep eyes.
    card.shape("eye-l", {"type": "path", "d": ellipse_path(470, 404, 42, 56)})
    card.shape("eye-r", {"type": "path", "d": ellipse_path(558, 404, 42, 56)})


def flats(card):
    for sid, color in [("robe", ROBE), ("arm-l", ROBE_LT), ("arm-r", ROBE_LT),
                       ("neck", SKIN_DK), ("head", SKIN), ("collar", ROBE_LT),
                       ("hand-l", SKIN), ("hand-r", SKIN), ("finger", SKIN),
                       ("eye-l", "#070d14"), ("eye-r", "#070d14")]:
        card.fill("flats", shape=sid, color=color, expand=2)


def light(card):
    card.light(["head"], depth=30, soft=2, rim_width=7, shade_color=SHADE,
               rim_color=RIM, strength=0.8)
    card.light(["robe", "arm-l", "arm-r"], depth=26, soft=2, rim_width=6,
               shade_color=SHADE, rim_color=RIM, strength=0.85)
    card.light(["neck", "collar", "hand-l", "hand-r", "finger"], depth=14,
               soft=1, rim_width=4, shade_color=SHADE, rim_color=RIM, strength=0.9)


def eyes(card):
    # Deep glossy eyes: a dark pool, a cool iris, and the astronaut mirrored as
    # a bright speck in each - the Visitor is looking right back.
    for cx in (470, 558):
        card.node("inlay", {"type": "ellipse", "cx": cx, "cy": 404, "rx": 40, "ry": 54,
                            "fill": radial(cx - 10, 388, 58,
                                           [[0, "#2a4a6a"], [0.55, "#101c30"],
                                            [1, "#05080e"]])})
        card.node("inlay", {"type": "ellipse", "cx": cx, "cy": 414, "rx": 18, "ry": 26,
                            "fill": "#02040a"})
        card.node("light", {"type": "ellipse", "cx": cx - 12, "cy": 384, "rx": 9, "ry": 13,
                            "fill": GLINT + "ee"})
        card.node("light", {"type": "ellipse", "cx": cx + 10, "cy": 420, "rx": 4, "ry": 5,
                            "fill": "#ffffffcc"})


def freckles(card):
    # Bioluminescent freckles scattered over the cheeks and brow, brightest
    # near the eyes, on a screen layer so they read as light under the skin.
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
    # The frill collar glows from under the chin.
    card.node("glow", {"type": "path", "d":
                       "M512 584 C 596 584 648 636 648 688 C 600 712 424 712 376 688 "
                       "C 376 636 428 584 512 584 Z",
                       "fill": radial(512, 660, 150,
                                      [[0, FRILL + "aa"], [0.6, FRILL + "33"],
                                       [1, FRILL + "00"]]),
                       "blur": 6})
    # Ribs of the frill, drawn as bright arcs.
    for i in range(7):
        t = i / 6
        x = 400 + t * 224
        card.node("glow", {"type": "path",
                           "d": f"M{x:.0f} 690 C {x:.0f} 648 {512 + (x - 512) * 0.4:.0f} 612 512 600",
                           "fill": "none",
                           "stroke": {"paint": FRILL + "88", "width": 2.5}})


def fingertip(card):
    # The glowing fingertip: the point of contact.
    card.node("glow", {"type": "ellipse", "cx": 718, "cy": 344, "rx": 60, "ry": 60,
                       "fill": radial(718, 344, 60,
                                      [[0, "#ffffffcc"], [0.3, FRILL + "aa"],
                                       [0.7, CYAN + "44"], [1, CYAN + "00"]])})
    card.node("light", {"type": "ellipse", "cx": 718, "cy": 344, "rx": 12, "ry": 14,
                        "fill": "#ffffffff"})
    # A few sparks drifting off the fingertip.
    for dx, dy, r in [(28, -18, 3), (-22, -30, 2.4), (40, 16, 2.2), (14, -44, 2)]:
        card.node("glow", {"type": "ellipse", "cx": 718 + dx, "cy": 344 + dy,
                           "rx": r, "ry": r,
                           "fill": radial(718 + dx, 344 + dy, r * 2,
                                          [[0, GLINT], [1, CYAN + "00"]])})


def ink(card):
    card.ink(weight=8, seed=3, shapes=["robe", "arm-l", "arm-r"])
    card.ink(weight=7, seed=4, shapes=["head", "neck"])
    card.ink(weight=5, seed=5, shapes=["collar", "hand-l", "hand-r", "finger"])
    card.ink(weight=5, seed=6, shapes=["eye-l", "eye-r"])


def build():
    card = Card()
    for name, color in [("ink", INK), ("skin", SKIN), ("robe", ROBE),
                        ("frill", FRILL), ("glow", CYAN)]:
        card.palette(name, color)
    sky(card, ACCENT, horizon=0.44)
    card.layer("sketch", "vector", visible=False)
    card.layer("flats", "paint")
    card.layer("shade", "paint", blend="multiply", opacity=0.82, clip=True)
    card.layer("rim", "paint", clip=True)
    card.layer("inlay", "vector")
    card.layer("glow", "vector", blend="screen")
    card.layer("lines", "paint")
    card.layer("light", "vector", blend="add")
    shapes(card)
    flats(card)
    light(card)
    eyes(card)
    freckles(card)
    collar_glow(card)
    fingertip(card)
    ink(card)
    card_frame(card, "03 / FIRST CONTACT", "THE VISITOR", ACCENT)
    card.dump()


if __name__ == "__main__":
    build()
