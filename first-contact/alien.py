"""Card 03 - THE VISITOR.

Purpose: the other side of the same moment. A tall, quiet being holds out one
finger, and the light at its tip is the only lamp in the triptych's last two
cards.
Focus: the lit fingertip, then the face it lights.
Light: the fingertip is the key, low and to the left, so the face is lit from
below and in front and the back of the skull goes to shadow. The sky gives a
blue rim on the far side.
Values: a dark robe against a lighter dusk, so the pale face and the hand are
the only bright shapes.
"""

from kit import (FRAMES, SKYLIGHT, Card, Rng, area, backdrop, blob, card_frame,
                 cast, clipped, curve, ellipse, halo, hexc, line, mix, motes,
                 radial, spot, tube, wave)

ACCENT = "#9dffcf"
MINT = "#bffff0"

SKIN = "#b4dcd2"
ROBE = "#463f86"
LINING = "#2a1f4e"
GOLD = "#e6bd6a"
INK = "#080616"

TIP = (84, 508)
WRIST = (269, 633)
SHOULDER = (838, 742)
NECK = (672, 560)

HEAD = blob([(640, 140), (725, 165), (785, 240), (800, 330), (775, 420),
             (725, 480), (680, 515), (630, 550), (585, 568), (552, 548),
             (536, 505), (524, 460), (506, 432), (512, 395), (500, 350),
             (505, 280), (540, 200), (585, 155)])
EYE = blob([(536, 404, 1), (556, 380), (592, 370), (628, 378), (648, 392, 1),
            (618, 418), (580, 430), (552, 422)])
FAR_EYE = blob([(498, 364), (512, 366), (522, 382), (516, 398), (502, 402)])
SLEEVE = blob([(850, 690), (760, 692), (640, 706), (520, 714), (452, 722),
               (436, 764), (454, 808), (514, 872), (580, 944), (646, 932),
               (744, 892), (846, 850), (896, 780)])
MOUTH = ellipse(452, 765, 17, 44, turn=-4)


def body(card):
    card.piece("body", bone="body", sizes=(34, 16, 8, 4), threshold=4)
    # The collar stands high behind the neck.
    back = blob([(596, 650), (640, 604), (716, 572), (768, 580), (792, 640),
                 (760, 700), (680, 690)])
    card.form(back, LINING, depth=50, soft=30, rim=0.6)
    neck = tube([(672, 500), (692, 592), (672, 712)], [48, 38, 54])
    card.form(neck, SKIN, depth=34, soft=20, rim=0.5, extra=[
        # The jaw's shadow.
        area(ellipse(640, 548, 90, 40, turn=-18), INK, blur=16, opacity=0.6),
        line(curve([(650, 600), (656, 650), (648, 700)]), INK, 5, blur=5,
             opacity=0.25),
    ])
    robe = blob([(590, 676), (530, 716), (478, 830), (446, 980), (432, 1190),
                 (966, 1190), (958, 980), (930, 850), (884, 748), (812, 688),
                 (748, 660), (670, 700)])
    folds = []
    for k, (top, low, strength) in enumerate([
            ((552, 730), (492, 1190), 0.5), ((596, 750), (566, 1190), 0.4),
            ((650, 780), (640, 1190), 0.3), ((716, 930), (712, 1190), 0.45),
            ((790, 910), (800, 1190), 0.4), ((860, 880), (884, 1190), 0.45),
            ((916, 850), (944, 1190), 0.35)]):
        mid = ((top[0] + low[0]) / 2 - 14 + 9 * (k % 3), (top[1] + low[1]) / 2)
        folds.append(line(curve([top, mid, low]), INK, 18, blur=12,
                          opacity=strength))
        folds.append(line(curve([(top[0] + 22, top[1]), (mid[0] + 24, mid[1]),
                                 (low[0] + 26, low[1])]),
                          hexc(card.lit(ROBE, mid[0], mid[1], 1.6)), 9, blur=9,
                          opacity=0.5))
    card.form(robe, ROBE, depth=150, soft=80, extra=[
        cast(SLEEVE, 20, 46, 30, 0.6), *folds])
    front = blob([(584, 650), (592, 712), (640, 744), (706, 742), (768, 708),
                  (796, 644), (778, 612), (764, 668), (716, 700), (660, 704),
                  (618, 682), (602, 640)])
    card.form(front, mix(ROBE, "#ffffff", 0.08), depth=24, soft=14, extra=[
        line(curve([(600, 648), (612, 690), (654, 714), (712, 710),
                    (760, 680), (780, 624)]), hexc(card.lit(GOLD, 640, 700)),
             3.5, blur=0.8, opacity=0.9),
    ])
    clasp = ellipse(628, 730, 12, 15, turn=-20)
    card.form(clasp, GOLD, depth=6, soft=3, edge=1.0)
    card.close()


def head(card):
    card.piece("head", bone="head", sizes=(26, 12, 6, 3), threshold=4)
    glint = hexc(card.lit("#ffffff", 560, 410, 1.6))
    # Skin like a sea creature's: a violet cast and darker speckles that
    # gather on the crown.
    rng = Rng(8)
    speckles = [area(ellipse(700, 300, 110, 130, turn=20), "#8f6cc4", blur=50,
                     opacity=0.35)]
    for _ in range(46):
        x = rng.span(560, 790)
        y = 150 + rng.next() ** 1.6 * 260
        r = rng.span(2.5, 8) * (1 - (y - 150) / 420)
        speckles.append(spot(x, y, r, r * rng.span(0.7, 1.0), "#2c4a66",
                             blur=1.6, opacity=rng.span(0.18, 0.4)))
    card.form(HEAD, SKIN, depth=150, soft=84, under=speckles, extra=[
        # The brow's shadow, the hollow of the cheek, and the skull's far side.
        area(ellipse(584, 360, 92, 24, turn=10), INK, blur=14, opacity=0.5),
        area(ellipse(612, 486, 64, 36, turn=-30), INK, blur=22, opacity=0.4),
        area(ellipse(560, 450, 46, 15, turn=18), "#ffffff", blur=9,
             opacity=0.32),
        area(ellipse(520, 318, 16, 44, turn=8), "#ffffff", blur=12,
             opacity=0.25),
        # The lower lids catch the light.
        line(curve([(548, 424), (580, 434), (620, 420)]), "#ffffff", 2.5,
             blur=2, opacity=0.4),
        line(curve([(520, 460), (526, 448), (522, 440)]), INK, 3, blur=1.5,
             opacity=0.6),
        line(curve([(540, 508), (556, 512), (574, 508)]), INK, 3.2, blur=1.2,
             opacity=0.65),
        line(curve([(544, 518), (556, 522), (568, 520)]), "#ffffff", 2, blur=2,
             opacity=0.18),
        # Faint ridges that run back over the skull.
        line(curve([(560, 240), (640, 196), (730, 220), (780, 300)]), INK, 5,
             blur=6, opacity=0.2),
        line(curve([(610, 300), (680, 270), (750, 300), (780, 380)]), INK, 5,
             blur=6, opacity=0.18),
    ])
    for eye, hi in ((EYE, (566, 404)), (FAR_EYE, (506, 384))):
        x0, y0, x1, y1 = eye.bbox
        card.node(card.cur.under, clipped(eye, [
            {"type": "rect", "x": x0, "y": y0, "w": x1 - x0, "h": y1 - y0,
             "fill": radial(hi[0], hi[1] + 6, (x1 - x0) * 0.8, [
                 [0, "#1c4a52"], [0.4, "#0c1830"], [1, "#04040c"]])},
            area(ellipse((x0 + x1) / 2, y0 - 2, (x1 - x0) * 0.5, 10), "#6a78d8",
                 blur=6, opacity=0.5),
            line(curve([(x0 + 4, hi[1] + 6), (hi[0], y1 - 5),
                        ((x0 + x1) / 2 + 12, y1 - 5)]), hexc(MINT, 0.55), 3,
                 blur=2.5),
            spot(hi[0], hi[1], 16, 12, hexc(MINT, 0.5), blur=7),
            spot(hi[0], hi[1], 5.5, 5.5, glint, blur=0.8),
            line(eye.d, "#000000", 5, blur=3, opacity=0.7),
        ]))
        card.fill(eye, "#080a16")
    card.close()


def arm(card):
    card.piece("arm", bone="arm", sizes=(28, 14, 7, 3.5), threshold=4)
    card.form(SLEEVE, ROBE, depth=110, soft=56, away=(0.5, 0.86), extra=[
        line(curve([(820, 720), (700, 790), (596, 900)]), INK, 16, blur=12,
             opacity=0.5),
        line(curve([(780, 706), (640, 760), (520, 840)]), INK, 12, blur=10,
             opacity=0.4),
        line(curve([(800, 712), (670, 772), (556, 866)]), "#ffffff", 6, blur=8,
             opacity=0.12),
        line(curve([(700, 700), (580, 738), (470, 780)]), INK, 9, blur=8,
             opacity=0.3),
    ], over=[
        # A gold border along the hem.
        line(curve([(454, 808), (514, 872), (580, 944), (646, 932), (744, 892),
                    (846, 850)]), hexc(card.lit(GOLD, 560, 900, 1.2)), 9,
             blur=0.8, opacity=0.9),
        line(curve([(470, 800), (526, 858), (584, 920), (642, 910), (740, 872),
                    (840, 832)]), hexc(card.lit(GOLD, 560, 880, 1.2)), 2,
             blur=0.6, opacity=0.7),
    ])
    card.form(MOUTH, LINING, flat=True, edge=0, rim=0, extra=[
        area(ellipse(446, 765, 12, 38, turn=-4), INK, blur=6, opacity=0.5),
    ], over=[
        line(MOUTH.d, hexc(card.lit(GOLD, 440, 760)), 3.5, blur=0.8,
             opacity=0.9),
    ])
    fore = tube([(456, 762), (366, 716), WRIST], [30, 23, 16])
    card.form(fore, SKIN, depth=18, soft=10, away=(0.45, 0.9), edge=0.9,
              extra=[
                  # The sleeve's shadow where the arm comes out of it.
                  area(ellipse(466, 768, 30, 44), INK, blur=14, opacity=0.6),
              ])
    card.close()


def reach(points, k=1.25):
    """Scale the hand's points out from the fingertip: long hands suit it."""
    return [(TIP[0] + (x - TIP[0]) * k, TIP[1] + (y - TIP[1]) * k)
            for x, y in points]


def finger(card, points, radii):
    points = reach(points)
    radii = [r * 1.25 for r in radii]
    card.form(tube(points, radii), SKIN, depth=radii[0] * 0.7,
              soft=radii[0] * 0.45, gain=1.2, away=(0.45, 0.9), edge=1.0,
              rim=0.6)


def hand(card):
    card.piece("hand", bone="hand", sizes=(12, 6, 3), threshold=4)
    finger(card, [(218, 606), (192, 622), (172, 616)], [8, 6.5, 5])
    palm = blob(reach([(244, 594), (222, 576), (196, 572), (180, 584),
                       (184, 606), (204, 618), (230, 622)]))
    card.form(palm, SKIN, depth=22, soft=12, gain=1.15, away=(0.45, 0.9),
              rim=0.6)
    finger(card, [(196, 610), (170, 616), (160, 632)], [6.5, 5.5, 4.5])
    finger(card, [(188, 602), (156, 604), (142, 620)], [7.5, 6, 5])
    finger(card, [(184, 592), (146, 584), (126, 598)], [8, 6.5, 5.5])
    finger(card, [(190, 580), (138, 542), (TIP[0] + 4, TIP[1] + 3)],
           [8.5, 6.5, 5])
    card.close()


def build():
    card = Card(panel=2, lamp=TIP, reach=540, power=1.4, rims=[
        (0.75, -0.66, SKYLIGHT, 9, 0.7)])
    backdrop(card)
    body(card)
    head(card)
    arm(card)
    hand(card)
    card.skeleton([
        ("body", None, (700, 1120), (690, 720)),
        ("head", "body", NECK, (650, 200)),
        ("arm", "body", SHOULDER, WRIST),
        ("hand", "arm", WRIST, TIP),
    ])
    # Marks that glow along the brow and under the eye.
    card.light_layer("marks", bone="head")
    rng = Rng(19)
    for x, y, size in [(602, 338, 4.6), (630, 320, 3.2), (662, 311, 5.2),
                       (700, 312, 3.6), (734, 326, 4.4), (762, 350, 2.8),
                       (780, 384, 2.2), (598, 452, 3.4), (617, 463, 2.4),
                       (640, 468, 1.8)]:
        x, y = x + rng.span(-4, 4), y + rng.span(-4, 4)
        card.node("marks", halo(x, y, size * 3.4, MINT, 0.8))
        card.node("marks", spot(x, y, size * 0.7, size * 0.6, "#f4fffb",
                                blur=0.6))
    card.pulse("marks", 0.35, 1.0, period=24)
    # The eyes close for two frames in each loop.
    card.light_layer("lids", bone="head", blend="normal")
    lid = hexc(card.lit(SKIN, 580, 400, 0.8))
    for eye in (EYE, FAR_EYE):
        card.node("lids", area(eye.grown(1.06), lid))
    card.node("lids", line(curve([(540, 410), (584, 424), (644, 396)]),
                           "#1a2440", 3, blur=0.8, opacity=0.8))
    for frame in range(FRAMES):
        card.key("lids", frame, ease="step",
                 opacity=1 if frame in (30, 31) else 0)
    card.light_layer("tip", bone="hand")
    card.node("tip", halo(TIP[0], TIP[1], 150, MINT, 1.0))
    card.node("tip", line(f"M{TIP[0] - 120} {TIP[1]} L{TIP[0] + 150} {TIP[1]}",
                          hexc(MINT, 0.7), 1.6, blur=1.2))
    card.node("tip", line(f"M{TIP[0]} {TIP[1] - 110} L{TIP[0]} {TIP[1] + 110}",
                          hexc(MINT, 0.7), 1.6, blur=1.2))
    card.node("tip", spot(TIP[0], TIP[1], 15, 15, "#ffffff", blur=5))
    card.node("tip", spot(TIP[0], TIP[1], 7, 7, "#ffffff", blur=1))
    card.pulse("tip", 0.8, 1.0)
    card.layer("glow", "vector", blend="screen")
    card.node("glow", {**halo(TIP[0], TIP[1], 460, MINT, 0.75), "id": "lampglow"})
    card.pulse("lampglow", 0.7, 1.0)
    motes(card, "motes", (190, 500), 16, 190, MINT, seed=4, drift=(30, -34))
    card_frame(card, "03 / FIRST CONTACT", "THE VISITOR", ACCENT)
    card.animate(lambda t: ({
        "body": 0.9 * wave(t, phase=0.5),
        "head": -3.6 * wave(t, phase=0.42),
        "arm": 3.4 * wave(t, phase=0.38),
        "hand": -6.5 * wave(t, phase=0.25) + 2.0 * wave(t, 2),
    }, (0, -8 * wave(t, phase=0.6))))
    return card


if __name__ == "__main__":
    build().run()
