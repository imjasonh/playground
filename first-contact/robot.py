"""Card 01 - THE ROBOT.

Purpose: an old machine that has kept one thing alive. A weathered robot bows
its head over a sprout it holds up in one hand.
Focus: the glowing bud, then the lens that looks at it.
Light: the bud is the key, so the robot is lit from below and in front: the
underside of the head, the top of the forearm and the cupped fingers. The
ringed planet, off to the right, gives a rose rim; the sky a dim blue one.
Values: the robot is a dark warm shape against the dusk, and the light pools
around the hand.
"""

from kit import (ROSE, SKYLIGHT, Card, Rng, area, backdrop, blob, card_frame,
                 cast, clipped, curve, ellipse, halo, hexc, line, mix, motes,
                 radial, spot, tube, wave)

ACCENT = "#ffc46b"
MINT = "#bffff0"
AMBER = "#ffb44a"

PAINT = "#e2a23e"
HULL = "#c88a36"
STEEL = "#8e96aa"
RUBBER = "#4a4854"
RUST = "#6e3418"
SOIL = "#6a4630"
LEAF = "#58c873"
INK = "#080616"

BUD = (668, 640)
HX, HY, TILT = 452, 372, 22
SHOULDER = (268, 668)
ELBOW = (330, 944)
WRIST = (566, 842)
ROOT = (662, 786)


def on_head(shape):
    """Put a shape drawn about the head's own centre onto the bowed head."""
    return shape.turned(TILT, (0, 0)).moved(HX, HY)


def hp(x, y):
    return on_head(blob([(x, y), (x + 1, y), (x, y + 1)])).parts[0][0]


def hcurve(points):
    return curve([hp(x, y) for x, y in points])


SKULL = on_head(blob([(-152, -40), (-140, -112), (-90, -160), (0, -178),
                      (92, -160), (152, -104), (172, -20), (170, 62),
                      (150, 114), (60, 132), (-60, 132), (-136, 102),
                      (-154, 30)]))
HOOD = on_head(blob([(-44, -112), (60, -140), (150, -112), (190, -60),
                     (186, -34), (150, -66), (62, -92), (-30, -72)]))
HOUSING = on_head(ellipse(72, 2, 80, 86))
LENS = on_head(ellipse(76, 4, 60, 66))
UPPER = tube([SHOULDER, (284, 810), ELBOW], [70, 62, 56])
FORE = tube([ELBOW, (450, 912), WRIST], [56, 52, 44])


def weather(shape, seed, count=7):
    """Rust blooms and chipped paint, placed inside a shape's bounds."""
    rng = Rng(seed)
    x0, y0, x1, y1 = shape.bbox
    marks = []
    for _ in range(count):
        x, y = rng.span(x0, x1), rng.span(y0, y1)
        r = rng.span(10, 34)
        marks.append(area(blob([(x - r, y), (x - r * 0.3, y - r * 0.6),
                                (x + r * 0.8, y - r * 0.3), (x + r, y + r * 0.4),
                                (x, y + r * 0.7)]), RUST, blur=r * 0.3,
                          opacity=rng.span(0.4, 0.75)))
        # Rust runs down from where it starts.
        marks.append(line(f"M{x:.0f} {y:.0f} L{x + rng.span(-4, 4):.0f} "
                          f"{y + rng.span(30, 90):.0f}", RUST, rng.span(3, 7),
                          blur=3, opacity=rng.span(0.25, 0.5)))
    for _ in range(count * 2):
        x, y = rng.span(x0, x1), rng.span(y0, y1)
        marks.append(spot(x, y, rng.span(1.5, 5), rng.span(1.5, 4), "#3a2a22",
                          blur=0.8, opacity=rng.span(0.3, 0.6)))
    return marks


def rivets(card, points):
    out = []
    for x, y in points:
        out.append(spot(x + 1.5, y + 2, 5, 5, INK, blur=2, opacity=0.5))
        out.append(spot(x, y, 3.6, 3.6, hexc(card.lit(STEEL, x, y, 0.8))))
    return out


def body(card):
    card.piece("body", bone="body", sizes=(32, 16, 8, 4), threshold=4)
    neck = tube([hp(-30, 90), (398, 540), (390, 600)], [64, 60, 66])
    ribs = [line(curve([(330, 486 + 22 * k), (396, 502 + 22 * k),
                        (462, 486 + 22 * k)]), INK, 5, blur=2.5, opacity=0.55)
            for k in range(5)]
    card.form(neck, RUBBER, depth=40, soft=20, rim=0.5, extra=ribs)
    torso = blob([(252, 592), (216, 700), (210, 850), (230, 1010), (250, 1190),
                  (652, 1190), (664, 1010), (654, 860), (624, 724), (566, 624),
                  (474, 578), (340, 572)])
    hatch = blob([(420, 716, 1), (584, 730, 1), (612, 930, 1), (430, 944, 1)],
                 n=3)
    card.form(torso, HULL, depth=170, soft=90, under=weather(torso, 5, 9),
              extra=[
        # The head's shadow on the chest, and the arm's.
        area(ellipse(430, 590, 190, 50), INK, blur=26, opacity=0.6),
        cast(UPPER + FORE, 22, 30, 22, 0.7),
        line(hatch.d, INK, 5, blur=2, opacity=0.6),
        line(hatch.moved(3, 3).d, "#ffffff", 2, blur=2, opacity=0.14),
        # A worn stripe across the hatch.
        line("M436 800 L596 812", hexc(card.lit("#2c2a30", 520, 806)), 26,
             blur=1.5, opacity=0.75),
        line("M250 1040 L660 1056", INK, 6, blur=3, opacity=0.45),
        *rivets(card, [(446, 740), (566, 750), (590, 914), (450, 924),
                       (300, 640), (540, 640), (270, 1010), (640, 1024)]),
        spot(470, 884, 6, 6, hexc(AMBER, 0.9)),
        spot(470, 884, 16, 16, hexc(AMBER, 0.5), blur=8),
    ])
    card.close()


def antenna(card):
    card.piece("antenna", bone="antenna", sizes=(8, 4), threshold=4, relief=1.5)
    base, kink, tip = hp(-78, -162), hp(-100, -230), hp(-80, -280)
    rod = tube([base, kink, tip], [6, 4.5, 3.5])
    card.form(rod, STEEL, depth=3, soft=2)
    card.form(ellipse(tip[0], tip[1], 9, 9), "#c8483c", depth=5, soft=3)
    card.close()
    return base, tip


def head(card):
    card.piece("head", bone="head", sizes=(26, 12, 6, 3), threshold=4)
    card.form(SKULL, PAINT, depth=170, soft=90, under=weather(SKULL, 9, 7),
              extra=[
        cast(HOOD, 4, 26, 16, 0.6),
        cast(HOUSING, -12, 6, 12, 0.45),
        # A seam over the crown, a dent, and vents on the jaw.
        line(hcurve([(-150, -30), (-80, -64), (20, -80)]), INK, 4, blur=2,
             opacity=0.5),
        area(on_head(ellipse(-84, -112, 30, 20, turn=-30)), INK, blur=10,
             opacity=0.35),
        *[line(hcurve([(18 + 26 * k, 100), (26 + 26 * k, 122)]), INK, 7,
               blur=1.2, opacity=0.75) for k in range(5)],
        *rivets(card, [hp(-120, 84), hp(-134, -6), hp(-60, 112)]),
    ])
    ear = on_head(ellipse(-92, 22, 44, 50))
    card.form(ear, STEEL, depth=30, soft=14, extra=[
        area(on_head(ellipse(-92, 22, 20, 23)), INK, blur=3, opacity=0.6),
        area(on_head(ellipse(-92, 22, 10, 12)),
             hexc(card.lit(STEEL, 350, 320, 1.2))),
    ])
    card.form(HOUSING, STEEL, depth=44, soft=18, edge=1.0)
    x0, y0, x1, y1 = LENS.bbox
    cx, cy = LENS.centre
    glint = hp(104, 44)
    card.node(card.cur.under, clipped(LENS, [
        {"type": "rect", "x": x0, "y": y0, "w": x1 - x0, "h": y1 - y0,
         "fill": radial(cx, cy, 66, [
             [0, "#2a0f04"], [0.22, "#b8560c"], [0.4, "#f0a23a"],
             [0.48, "#5a2606"], [0.7, "#160b0c"], [1, "#05040a"]])},
        spot(cx, cy, 13, 13, "#050308"),
        area(on_head(ellipse(60, -30, 46, 20, turn=-20)), "#5560c0", blur=10,
             opacity=0.45),
        # The bud, seen in the glass.
        halo(glint[0], glint[1], 26, MINT, 0.9),
        spot(glint[0], glint[1], 4, 4, "#ffffff", blur=0.8),
        line(hcurve([(30, -34), (44, -48), (66, -56)]), "#ffffff", 3, blur=1.2,
             opacity=0.6),
        line(LENS.d, "#000000", 8, blur=4, opacity=0.7),
    ]))
    card.fill(LENS, "#160b0c")
    card.form(HOOD, mix(PAINT, "#000000", 0.12), depth=30, soft=14,
              under=weather(HOOD, 13, 2))
    card.close()


def arm(card):
    card.piece("arm", bone="arm", sizes=(28, 14, 7, 3.5), threshold=4)
    card.form(UPPER, PAINT, depth=60, soft=30, under=weather(UPPER, 21, 4),
              extra=[
        line(curve([(210, 760), (280, 772), (352, 756)]), INK, 5, blur=2,
             opacity=0.5),
    ])
    pauldron = blob([(160, 660), (176, 590), (240, 552), (320, 560),
                     (374, 616), (380, 690), (344, 748), (262, 768),
                     (188, 734)])
    card.form(pauldron, PAINT, depth=90, soft=46, under=weather(pauldron, 17, 5),
              extra=[
        line(curve([(180, 700), (262, 730), (356, 706)]), INK, 5, blur=2,
             opacity=0.5),
        *rivets(card, [(206, 690), (262, 708), (326, 694)]),
    ])
    card.form(FORE, PAINT, depth=50, soft=26, under=weather(FORE, 25, 4),
              extra=[
        cast(ellipse(ELBOW[0], ELBOW[1], 62, 62), 14, -6, 12, 0.5),
        # Hazard bands near the wrist.
        line("M484 852 L512 944", hexc(card.lit("#2c2a30", 500, 890)), 16,
             blur=1.2, opacity=0.8),
        line("M516 842 L542 930", hexc(card.lit("#2c2a30", 530, 880)), 16,
             blur=1.2, opacity=0.8),
    ])
    joint = ellipse(ELBOW[0], ELBOW[1], 60, 60)
    card.form(joint, STEEL, depth=44, soft=22, extra=[
        area(ellipse(ELBOW[0], ELBOW[1], 24, 24), INK, blur=3, opacity=0.55),
        area(ellipse(ELBOW[0], ELBOW[1], 12, 12),
             hexc(card.lit(STEEL, ELBOW[0], ELBOW[1], 1.2))),
    ])
    card.close()


def claw(card, points, radii):
    shape = tube(points, radii)
    card.form(shape, STEEL, depth=radii[0] * 0.9, soft=radii[0] * 0.5,
              gain=1.15, edge=1.0, extra=[
                  line(curve([points[1], (points[1][0] + 10, points[1][1] + 6)]),
                       INK, 4, blur=2, opacity=0.5),
              ])


def hand(card):
    card.piece("hand", bone="hand", sizes=(18, 9, 4.5), threshold=4)
    cuff = ellipse(WRIST[0], WRIST[1], 22, 50, turn=-24)
    card.form(cuff, RUBBER, depth=20, soft=10, gain=1.2)
    claw(card, [(716, 818), (752, 776), (748, 726)], [19, 17, 13])
    claw(card, [(690, 806), (726, 760), (716, 712)], [19, 17, 13])
    palm = blob([(560, 816), (606, 802), (700, 806), (730, 826), (712, 856),
                 (650, 872), (584, 866), (552, 844)])
    card.form(palm, STEEL, depth=40, soft=20, gain=1.1, extra=[
        line(curve([(580, 840), (650, 850), (716, 836)]), INK, 4, blur=2,
             opacity=0.45),
    ])
    soil = blob([(600, 812), (612, 786), (640, 772), (676, 772), (702, 790),
                 (712, 814), (656, 822)])
    rng = Rng(41)
    crumbs = [spot(rng.span(606, 706), rng.span(778, 812), rng.span(2, 5),
                   rng.span(1.5, 4), hexc(card.lit(SOIL, 660, 780, 1.6)),
                   blur=0.8, opacity=rng.span(0.4, 0.9)) for _ in range(16)]
    card.form(soil, SOIL, depth=16, soft=10, gain=1.3, rim=0.3, extra=crumbs)
    card.close()


def sprout(card):
    card.piece("sprout", bone="sprout", sizes=(8, 4, 2), threshold=3,
               relief=1.4)
    stem = tube([ROOT, (656, 730), (664, 690), BUD], [5, 4.5, 4, 3.5])
    left = blob([(660, 716, 1), (636, 716), (606, 698), (590, 672, 1),
                 (622, 676), (648, 694)])
    right = blob([(664, 700, 1), (684, 690), (716, 676), (742, 650, 1),
                  (708, 652), (680, 668)])
    for leaf, vein in ((left, [(658, 714), (626, 696), (594, 674)]),
                       (right, [(666, 698), (702, 676), (738, 652)])):
        card.form(leaf, LEAF, depth=9, soft=5, gain=0.75, rim=0.4, extra=[
            line(curve(vein), "#eafff0", 1.6, blur=0.8, opacity=0.6)])
    card.form(stem, LEAF, depth=3, soft=2, gain=0.8, rim=0)
    bud = blob([(BUD[0], BUD[1] - 20, 1), (BUD[0] + 12, BUD[1] - 4),
                (BUD[0] + 8, BUD[1] + 10), (BUD[0] - 8, BUD[1] + 10),
                (BUD[0] - 12, BUD[1] - 4)])
    card.form(bud, "#eafff4", flat=True, gain=3, edge=0, rim=0)
    card.close()


def thumb(card):
    card.piece("thumb", bone="hand", sizes=(14, 7, 3.5), threshold=4)
    claw(card, [(590, 846), (572, 798), (594, 754)], [21, 19, 14])
    knuckle = ellipse(592, 848, 24, 24)
    card.form(knuckle, STEEL, depth=16, soft=8, gain=1.1, extra=[
        area(ellipse(592, 848, 9, 9), INK, blur=2, opacity=0.55)])
    card.close()


def build():
    card = Card(panel=0, lamp=BUD, reach=320, power=1.5, rims=[
        (0.86, -0.5, ROSE, 9, 0.7), (-0.5, -0.86, SKYLIGHT, 6, 0.4)])
    backdrop(card)
    body(card)
    base, tip = antenna(card)
    head(card)
    arm(card)
    hand(card)
    sprout(card)
    thumb(card)
    card.skeleton([
        ("body", None, (440, 1120), (430, 640)),
        ("head", "body", hp(-34, 110), hp(0, -170)),
        ("antenna", "head", base, tip),
        ("arm", "body", SHOULDER, ELBOW),
        ("hand", "arm", WRIST, (700, 800)),
        ("sprout", "hand", ROOT, BUD),
    ])
    card.light_layer("beacon", bone="antenna")
    card.node("beacon", halo(tip[0], tip[1], 30, "#ff5a48", 1.0))
    card.node("beacon", spot(tip[0], tip[1], 3.5, 3.5, "#ffe1d6", blur=0.8))
    card.pulse("beacon", 0.1, 1.0, period=24, phase=0.3)
    # The lens has a light of its own, which breathes.
    card.light_layer("iris", bone="head")
    cx, cy = LENS.centre
    card.node("iris", halo(cx, cy, 80, AMBER, 0.55))
    card.pulse("iris", 0.45, 1.0)
    card.light_layer("budglow", bone="sprout")
    card.node("budglow", halo(BUD[0], BUD[1], 130, MINT, 1.0))
    card.node("budglow", spot(BUD[0], BUD[1], 13, 15, "#ffffff", blur=5))
    card.node("budglow", spot(BUD[0], BUD[1] - 2, 5, 7, "#ffffff", blur=1))
    card.pulse("budglow", 0.8, 1.0)
    card.layer("glow", "vector", blend="screen")
    card.node("glow", {**halo(BUD[0], BUD[1], 400, MINT, 0.6), "id": "lampglow"})
    card.pulse("lampglow", 0.7, 1.0)
    motes(card, "motes", (668, 600), 16, 150, MINT, seed=12, drift=(8, -46))
    card_frame(card, "01 / FIRST CONTACT", "THE ROBOT", ACCENT)
    card.animate(lambda t: ({
        "body": 0.8 * wave(t),
        "head": 4.0 * wave(t, phase=-0.1),
        "antenna": 9 * wave(t, 2, phase=-0.2),
        "arm": -2.0 * wave(t, phase=0.2),
        "hand": 3.5 * wave(t, phase=0.05),
        "sprout": 9 * wave(t, phase=-0.15) + 3.5 * wave(t, 2),
    }, (0, -8 * wave(t, phase=0.15))))
    return card


if __name__ == "__main__":
    build().run()
