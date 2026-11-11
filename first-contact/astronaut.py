"""Card 02 - THE ASTRONAUT.

Purpose: the moment before touch. An astronaut, far from home, leans in and
reaches a glove towards a light just outside the frame.
Focus: the gold visor and the reaching glove.
Light: the Visitor's fingertip, off the right edge (it is on card 03), is the
key. The ringed planet behind gives a rose rim; the sky a dim blue one.
Values: a dark sky and a middle-value planet; the suit sits in violet shadow
and only the planes facing the light go bright, brightest at the fingertips.
"""

from kit import (ROSE, SKYLIGHT, Card, area, backdrop, blob, card_frame, cast,
                 clipped, curve, ellipse, halo, hexc, line, mix, motes, radial,
                 spot, tube, wave, Shape)

ACCENT = "#79e7ff"
MINT = "#bffff0"

SUIT = "#e4e1da"
PACK = "#bfc0c6"
STEEL = "#8b94a8"
RUBBER = "#6f7686"
RED = "#d0473a"
INK = "#080616"

LAMP = (1148, 508)



def bubble():
    """The helmet: a sphere cut off where it meets the neck ring."""
    pts = []
    for x, y in ellipse(408, 392, 174, 178).parts[0]:
        if abs(x - 408) < 122:
            y = min(y, 524 + 30 * (1 - ((x - 408) / 122) ** 2) ** 0.5)
        pts.append((x, y))
    return Shape(pts)


HELMET = bubble()
VISOR = ellipse(462, 400, 118, 142, turn=4)
BEZEL = ellipse(459, 400, 133, 157, turn=4)
SLEEVE = tube([(372, 704), (484, 736), (586, 746), (684, 706), (760, 642)],
              [88, 76, 64, 54, 46])
WRIST = (770, 634)


def body(card):
    card.piece("body", bone="body", sizes=(30, 15, 7, 3.5), threshold=4)
    # The life-support pack rides high on the back.
    pack = blob([(176, 500), (196, 462), (262, 448), (320, 468), (338, 560),
                 (340, 1190), (166, 1190), (158, 820), (164, 600)])
    card.form(pack, PACK, depth=70, soft=40, extra=[
        line(curve([(170, 650), (240, 640), (320, 650)]), INK, 3, blur=1.5,
             opacity=0.5),
        line(curve([(164, 920), (240, 910), (320, 920)]), INK, 3, blur=1.5,
             opacity=0.5),
    ])
    mast = tube([(206, 470), (198, 400), (190, 338)], [4.5, 3.5, 2.5])
    card.form(mast, STEEL, depth=2, soft=1.5)
    torso = blob([(300, 546), (262, 606), (250, 700), (248, 820), (260, 960),
                  (272, 1190), (606, 1190), (602, 1040), (590, 930), (582, 820),
                  (572, 716), (560, 630), (522, 552), (410, 536)])
    card.form(torso, SUIT, depth=120, soft=64, extra=[
        # The helmet's shadow on the collar and the arm's across the chest.
        area(ellipse(410, 590, 190, 44), INK, blur=22, opacity=0.6),
        cast(SLEEVE, -30, 44, 26, 0.6),
        line(curve([(300, 1010), (400, 1046), (520, 1040), (600, 1056)]), INK,
             10, blur=8, opacity=0.3),
        # Creases that run from the armpit.
        line(curve([(430, 800), (400, 870), (410, 950)]), INK, 12, blur=9,
             opacity=0.28),
        line(curve([(500, 806), (490, 860), (506, 930)]), INK, 10, blur=8,
             opacity=0.25),
        line(curve([(452, 800), (430, 872), (436, 950)]), "#ffffff", 5, blur=6,
             opacity=0.1),
        line(curve([(560, 930), (500, 960), (470, 1010)]), INK, 9, blur=7,
             opacity=0.3),
    ])
    # The chest unit hangs in front. Its side faces us and its face the light.
    side = blob([(540, 800, 1), (622, 806, 1), (630, 968, 1), (550, 964, 1)],
                n=2)
    card.form(side, mix(PACK, "#30323c", 0.35), depth=60, soft=30, extra=[
        cast(SLEEVE, -10, 40, 14, 0.7),
        area(blob([(560, 862, 1), (606, 864, 1), (608, 892, 1), (562, 890, 1)],
                  n=2), "#0b1014"),
        line("M568 872 L598 873", hexc(MINT, 0.9), 2.2, blur=0.5),
        line("M568 882 L588 883", hexc(MINT, 0.55), 2.2, blur=0.5),
        spot(574, 926, 9, 9, "#2a2c34"), spot(574, 926, 4, 4, "#9aa0ac"),
        spot(602, 928, 5, 5, "#ff5a48"),
        spot(602, 928, 13, 13, "#ff5a48", blur=7, opacity=0.6),
    ])
    face = blob([(622, 806, 1), (644, 816, 1), (650, 962, 1), (630, 968, 1)],
                n=2)
    card.form(face, PACK, gain=1.5, flat=True, edge=0, rim=0)
    hose = tube([(566, 962), (530, 1020), (430, 1046), (332, 1010)],
                [13, 13, 13, 13])
    card.form(hose, "#c4c6d0", depth=10, soft=5, rim=0.4)
    card.close()


def arm(card):
    card.piece("arm", bone="arm", sizes=(26, 13, 6, 3), threshold=4)
    stripe = hexc(card.lit(RED, 520, 740, 1.0))
    card.form(SLEEVE, SUIT, depth=58, soft=30, away=(-0.45, 0.89), extra=[
        # The shoulder bearing, then the bellows at the elbow.
        line(curve([(440, 648), (462, 730), (446, 812)]), INK, 5, blur=3,
             opacity=0.45),
        line(curve([(520, 676), (540, 742), (528, 806)]), stripe, 20, blur=1.5),
        line(curve([(590, 680), (606, 742), (596, 800)]), INK, 8, blur=5,
             opacity=0.4),
        line(curve([(622, 672), (642, 728), (638, 788)]), INK, 8, blur=5,
             opacity=0.4),
        line(curve([(654, 656), (678, 708), (680, 764)]), INK, 7, blur=5,
             opacity=0.35),
        # A mission patch on the shoulder: the ringed world.
        spot(382, 690, 34, 38, "#1c2452"),
        spot(382, 690, 16, 17, "#d0609a"),
        line("M352 700 L412 680", "#ffd9cf", 2.5, opacity=0.9),
    ])
    card.close()


def big(points, k=1.15, about=(796, 620)):
    """Scale glove points up from the wrist: the glove is a bulky thing."""
    return [(WRIST[0] + (x - about[0]) * k, WRIST[1] + (y - about[1]) * k)
            for x, y in points]


def finger(card, points, radii, tip=13):
    points = big(points)
    radii = [r * 1.15 for r in radii]
    tip *= 1.15
    shape = tube(points, radii)
    x, y = points[-1]
    card.form(shape, SUIT, depth=radii[0] * 0.8, soft=radii[0] * 0.45,
              gain=1.25, away=(-0.3, 0.95), edge=1.0, extra=[
                  spot(x, y, tip * 1.5, tip * 1.25,
                       hexc(card.lit(RUBBER, x, y, 1.3)), blur=2.5),
                  line(curve([points[1], (points[1][0] + 3, points[1][1] + 12)]),
                       INK, 2.5, blur=2, opacity=0.35),
              ])


def hand(card):
    card.piece("hand", bone="hand", sizes=(14, 7, 3.5), threshold=4)
    # The back of the glove, thumb uppermost, first finger out to the light.
    finger(card, [(842, 574), (868, 542), (900, 524)], [16, 14.5, 12])
    palm = blob(big([(800, 574), (838, 552), (878, 548), (902, 572),
                     (902, 606), (884, 630), (846, 640), (812, 628)]))
    card.form(palm, SUIT, depth=36, soft=20, gain=1.2, away=(-0.3, 0.95),
              extra=[
                  line(curve(big([(878, 556), (890, 590), (876, 628)])), INK,
                       4, blur=3, opacity=0.4),
                  area(blob(big([(820, 580), (850, 568), (866, 590),
                                 (850, 614), (822, 610)])),
                       hexc(card.lit(RUBBER, 830, 600)), blur=3, opacity=0.8),
              ])
    finger(card, [(876, 620), (906, 632), (924, 648)], [12.5, 11, 9.5], tip=10)
    finger(card, [(884, 604), (926, 608), (952, 622)], [14, 12.5, 11], tip=11)
    finger(card, [(888, 586), (936, 582), (970, 588)], [15, 13.5, 11.5], tip=12)
    finger(card, [(882, 566), (932, 550), (980, 538)], [15, 13.5, 11.5], tip=12)
    cuff = ellipse(WRIST[0], WRIST[1], 19, 56, turn=-40)
    card.form(cuff, STEEL, depth=14, soft=7, edge=1.0)
    card.close()


def head(card):
    card.piece("head", bone="head", sizes=(26, 12, 6, 3), threshold=4)
    card.form(HELMET, SUIT, depth=150, soft=80, extra=[
        line(curve([(250, 330), (304, 250), (394, 212)]), INK, 4, blur=3,
             opacity=0.25),
        cast(BEZEL, -16, 8, 14, 0.4),
    ])
    card.form(BEZEL, "#b4b8c2", depth=40, soft=18, edge=0.9)
    ring = tube([(288, 526), (334, 549), (408, 557), (482, 549), (528, 526)],
                [13, 15, 16, 15, 13])
    card.form(ring, "#c2c8d6", depth=13, soft=6, edge=1.0, over=[
        line(curve([(300, 528), (340, 543), (408, 549), (476, 542),
                    (518, 526)]), "#e9f2ff", 2, blur=0.8, opacity=0.5),
    ])
    gold = "#f6bd6c"
    horizon = [(338, 470), (400, 492), (462, 499), (526, 488), (582, 462)]
    kids = [
        {"type": "rect", "x": 320, "y": 240, "w": 300, "h": 330,
         "fill": radial(470, 388, 170, [
             [0, "#100a0c"], [0.45, "#22130c"], [0.78, "#62380f"],
             [0.93, "#b8741f"], [1, "#e8a740"]])},
        area(ellipse(440, 330, 104, 56, turn=-12), "#232458", blur=30,
             opacity=0.7),
        # The plain reflected: its horizon bows across the glass.
        area(blob([(horizon[0][0] - 20, horizon[0][1] - 8, 1), *horizon[1:4],
                   (600, 452, 1), (606, 580, 1), (318, 580, 1)]),
             "#1c0e12", blur=2, opacity=0.85),
        line(curve(horizon), "#d2685c", 22, blur=11, opacity=0.6),
        line(curve(horizon), gold, 3.5, blur=1.4, opacity=0.95),
        # The Visitor, small in the glass, holding out one lit finger.
        area(blob([(498, 500), (502, 470), (512, 452), (528, 450), (544, 462),
                   (556, 500)]), "#1a1740"),
        area(tube([(520, 452), (518, 436)], [5, 4.5]), "#5f8f8c"),
        area(ellipse(516, 418, 13, 18, turn=-10), "#8fc4bc"),
        area(ellipse(521, 421, 12, 17, turn=-10), "#22404a", blur=3,
             opacity=0.8),
        spot(509, 420, 2.6, 1.8, "#04060c"),
        area(tube([(512, 462), (490, 462), (472, 452)], [4, 3, 2]), "#7fb4ae"),
        halo(468, 449, 52, MINT, 0.9),
        spot(468, 449, 4.5, 4.5, "#ffffff", blur=0.8),
        line("M442 449 L494 449", hexc(MINT, 0.8), 1.3, blur=0.8),
        line("M468 430 L468 468", hexc(MINT, 0.8), 1.3, blur=0.8),
        # The astronaut's own arm, reaching into the reflection.
        area(tube([(600, 520), (540, 492), (492, 464)], [20, 12, 5]),
             "#8d8fb4", blur=2.5, opacity=0.55),
        # Stars and the sheen of the glass.
        spot(396, 318, 1.6, 1.6, "#ffffff"), spot(452, 296, 1.3, 1.3, "#ffffff"),
        spot(514, 330, 1.5, 1.5, "#ffffff"), spot(420, 372, 1.2, 1.2, "#ffffff"),
        spot(548, 368, 1.2, 1.2, "#ffffff"),
        area(ellipse(396, 322, 74, 24, turn=-50), "#ffffff", blur=16,
             opacity=0.14),
        line(curve([(356, 376), (368, 318), (410, 272)]), "#ffffff", 3,
             blur=1.4, opacity=0.5),
        line(VISOR.d, "#000000", 7, blur=4, opacity=0.6),
    ]
    card.node(card.cur.under, clipped(VISOR, kids))
    card.fill(VISOR, "#150d10")
    card.close()


def build():
    card = Card(panel=1, lamp=LAMP, reach=620, power=1.5, rims=[
        (-0.86, -0.5, ROSE, 10, 0.85), (0.0, -1.0, SKYLIGHT, 6, 0.45)])
    backdrop(card)
    body(card)
    head(card)
    arm(card)
    hand(card)
    card.skeleton([
        ("body", None, (430, 1120), (430, 640)),
        ("head", "body", (408, 545), (408, 300)),
        ("arm", "body", (384, 706), WRIST),
        ("hand", "arm", WRIST, (960, 560)),
    ])
    card.light_layer("beacon", bone="body")
    card.node("beacon", halo(190, 336, 30, "#ff5a48", 1.0))
    card.node("beacon", spot(190, 336, 3.5, 3.5, "#ffe1d6", blur=0.8))
    card.pulse("beacon", 0.05, 1.0, period=24)
    card.layer("glow", "vector", blend="screen")
    card.node("glow", {**halo(LAMP[0], LAMP[1], 560, MINT, 0.95), "id": "lampglow"})
    card.pulse("lampglow", 0.7, 1.0)
    motes(card, "motes", (1000, 520), 14, 170, MINT, seed=7, drift=(-40, -30))
    card_frame(card, "02 / FIRST CONTACT", "THE ASTRONAUT", ACCENT)
    card.animate(lambda t: ({
        "body": 1.1 * wave(t),
        "head": 4.0 * wave(t, phase=-0.08),
        "arm": -5.0 * wave(t, phase=-0.12),
        "hand": 7.5 * wave(t, phase=-0.25) + 2.5 * wave(t, 2),
    }, (0, -9 * wave(t, phase=0.1))))
    return card


if __name__ == "__main__":
    build().run()
