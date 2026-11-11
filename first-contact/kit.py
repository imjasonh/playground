"""Shared drawing kit for the First Contact triptych.

Each card generator imports this module, blocks its subject in as vector
sketch shapes, and emits klad `apply` ops as JSON lines. The ops fill flat
colour, light each shape (a multiply shade and a rim), ink the outlines, add
glow on blend layers, and letter the card. Pipe the output into `klad apply`.
"""

import json
import math

# The key light for the whole triptych: high and a little to the left, so the
# three figures read as lit by the same star. KEY warms the lit side; SHADOW is
# a cool lavender the shadow side turns towards, so paint never goes muddy brown.
LIGHT = [-0.72, -0.62]
KEY = "#fff1dc"
SHADOW = "#5a5ea0"

# Each card is a tall tarot-sized panel; the triptych stands them side by side.
CARD_W = 1024
CARD_H = 1280

# One palette across the three cards. The dusk sky and the warm skin of each
# figure stay the same; each card keeps one accent that its glow and frame use.
SKY_TOP = "#0a0a1e"
SKY_LOW = "#241041"
STAR = "#cfe6ff"
CYAN = "#79e7ff"
MAGENTA = "#ff6fd0"
AMBER = "#ffbf73"


def linear(x1, y1, x2, y2, stops):
    return {"linear": {"from": [x1, y1], "to": [x2, y2], "stops": stops}}


def radial(cx, cy, r, stops):
    return {"radial": {"center": [cx, cy], "radius": r, "stops": stops}}


def ellipse_path(cx, cy, rx, ry):
    """A closed ellipse as an SVG path, so ink and light treat it as an area."""
    k = 0.5522847498
    ox, oy = rx * k, ry * k
    return (f"M{cx - rx} {cy} "
            f"C {cx - rx} {cy - oy} {cx - ox} {cy - ry} {cx} {cy - ry} "
            f"C {cx + ox} {cy - ry} {cx + rx} {cy - oy} {cx + rx} {cy} "
            f"C {cx + rx} {cy + oy} {cx + ox} {cy + ry} {cx} {cy + ry} "
            f"C {cx - ox} {cy + ry} {cx - rx} {cy + oy} {cx - rx} {cy} Z")


def rrect_path(x, y, w, h, r):
    """A rounded rectangle as a closed path."""
    r = min(r, w / 2, h / 2)
    x2, y2 = x + w, y + h
    return (f"M{x + r} {y} L{x2 - r} {y} Q{x2} {y} {x2} {y + r} "
            f"L{x2} {y2 - r} Q{x2} {y2} {x2 - r} {y2} "
            f"L{x + r} {y2} Q{x} {y2} {x} {y2 - r} "
            f"L{x} {y + r} Q{x} {y} {x + r} {y} Z")


def wobble(cx, cy, r, points, jitter, seed):
    """A closed blobby path: a ring of `points` with a seeded radial jitter."""
    rng = _Rng(seed)
    pts = []
    for i in range(points):
        a = 2 * math.pi * i / points
        rr = r * (1 + jitter * (rng.next() - 0.5))
        pts.append((cx + rr * math.cos(a), cy + rr * math.sin(a)))
    d = f"M{pts[0][0]:.1f} {pts[0][1]:.1f} "
    for i in range(points):
        a = pts[i]
        b = pts[(i + 1) % points]
        mx, my = (a[0] + b[0]) / 2, (a[1] + b[1]) / 2
        d += f"Q {a[0]:.1f} {a[1]:.1f} {mx:.1f} {my:.1f} "
    return d + "Z"


def _perp(dx, dy):
    length = math.hypot(dx, dy) or 1.0
    return -dy / length, dx / length


def limb_capsule(anchor, elbow, wrist, w_shoulder, w_elbow, w_wrist):
    """A two-segment limb outline: shoulder to elbow to wrist, tapered width."""
    pts = (anchor + (w_shoulder,), elbow + (w_elbow,), wrist + (w_wrist,))
    left, right = [], []
    for i, (px, py, half) in enumerate(pts):
        dx, dy = (pts[i + 1][0] - px, pts[i + 1][1] - py) if i < 2 else (
            px - pts[i - 1][0], py - pts[i - 1][1])
        pxp, pyp = _perp(dx, dy)
        left.append((px + pxp * half, py + pyp * half))
        right.append((px - pxp * half, py - pyp * half))
    l0, l1, l2 = left
    r0, r1, r2 = right

    def cubic(a, b):
        c1 = (a[0] + (b[0] - a[0]) * 0.35, a[1] + (b[1] - a[1]) * 0.35)
        c2 = (b[0] - (b[0] - a[0]) * 0.35, b[1] - (b[1] - a[1]) * 0.35)
        return (f"C {c1[0]:.1f} {c1[1]:.1f} {c2[0]:.1f} {c2[1]:.1f} "
                f"{b[0]:.1f} {b[1]:.1f} ")

    return (f"M{l0[0]:.1f} {l0[1]:.1f} "
            f"{cubic(l0, l1)}"
            f"{cubic(l1, l2)}"
            f"L{r2[0]:.1f} {r2[1]:.1f} "
            f"{cubic(r2, r1)}"
            f"{cubic(r1, r0)}"
            f"Z")


def almond_path(cx, cy, rx, ry, tilt_deg=0):
    """An asymmetric almond eye, not a perfect ellipse."""
    t = math.radians(tilt_deg)
    cos_t, sin_t = math.cos(t), math.sin(t)
    inner = rx * 0.52
    d = (f"M{cx - rx:.1f} {cy:.1f} "
         f"C {cx - rx * 0.2:.1f} {cy - ry:.1f} {cx + inner:.1f} {cy - ry * 0.85:.1f} "
         f"{cx + rx:.1f} {cy:.1f} "
         f"C {cx + inner:.1f} {cy + ry * 0.92:.1f} {cx - rx * 0.15:.1f} {cy + ry:.1f} "
         f"{cx - rx:.1f} {cy:.1f} Z")
    if abs(tilt_deg) < 0.5:
        return d
    # Caller can rotate via sketch transform; path is left axis-aligned for ink.
    return d



class _Rng:
    """A tiny deterministic generator, so a seed always draws the same card."""

    def __init__(self, seed):
        self.state = (seed * 2654435761 + 12345) & 0xFFFFFFFF

    def next(self):
        self.state = (self.state * 1103515245 + 12345) & 0x7FFFFFFF
        return self.state / 0x7FFFFFFF


class Card:
    """Accumulates apply ops for one card and prints them as JSON lines."""

    def __init__(self):
        self.ops = []
        self._seed = 0
        self.paint_layers = []
        # Line weight multiplier, so a card can dial its outlines down to let
        # the paint carry the silhouette.
        self.ink_scale = 0.45

    def op(self, obj):
        self.ops.append(obj)
        return obj

    def seed(self):
        self._seed += 1
        return self._seed

    def palette(self, name, color):
        self.op({"op": "palette", "add": color, "name": name})

    def layer(self, lid, kind, **extra):
        self.op({"op": "add", "layer": {"id": lid, "kind": kind, "name": lid, **extra}})

    def node(self, layer, node):
        self.op({"op": "add", "node": node, "in": layer})

    def shape(self, sid, node):
        self.op({"op": "add", "node": {**node, "id": sid}, "in": "sketch"})

    def fill(self, layer, **kw):
        self.op({"op": "fill", "layer": layer, **kw})

    def light(self, shapes, depth, soft, rim_width, shade_color, rim_color,
              strength=0.8):
        self.op({"op": "light", "from": shapes, "light": LIGHT,
                 "shade": "shade", "rim": "rim", "depth": depth, "soft": soft,
                 "shadeColor": shade_color, "rimColor": rim_color,
                 "rimWidth": rim_width, "shadeOpacity": strength})

    def paint_form(self, lid, shapes, color, relief=(4.0, 3.5), brush="oil",
                   weight=15, decisive=0.7, **extra):
        """Paint `shapes` as lit forms on their own layer, then light the oil.

        Fills the flat colour, locks alpha so strokes stay inside the shapes,
        paints each one as a form coloured by the key light with a cool shadow,
        and adds a relief effect so the oil body catches the same light. This is
        what makes the figure read as paint instead of a flat vector fill.
        """
        self.layer(lid, "paint")
        self.paint_layers.append(lid)
        for sid in shapes:
            self.fill(lid, shape=sid, color=color)
        self.op({"op": "set", "id": lid, "lockAlpha": True})
        self.op({"op": "paint", "layer": lid, "in": shapes, "light": LIGHT,
                 "key": KEY, "color": color, "brush": brush, "weight": weight,
                 "decisive": decisive, "fillStrength": 0.3,
                 "bounceStrength": 0.16, "shadow": SHADOW, "shadowMix": 0.68,
                 "seed": self.seed(), **extra})
        self.op({"op": "set", "id": lid, "lockAlpha": False})
        if relief:
            strength, softness = relief
            self.op({"op": "set", "id": lid, "effects": [
                {"relief": {"light": LIGHT, "highlight": KEY,
                            "strength": strength, "softness": softness}}]})

    def hatch(self, lid, shapes, angle, spacing, length, color, **kw):
        self.op({"op": "hatch", "layer": lid, "in": shapes, "angle": angle,
                 "spacing": spacing, "length": length, "color": color, **kw})

    def ink(self, weight, seed, shapes=None, path=None, color="ink",
            wobble=1.4, **kw):
        base = {"op": "ink", "layer": "lines", "light": LIGHT,
                "weight": weight * self.ink_scale, "color": color,
                "seed": seed, "wobble": wobble, **kw}
        self.op({**base, "path": path} if path else {**base, "from": shapes})

    def dump(self):
        print("\n".join(json.dumps(o) for o in self.ops))

    def brushwork(self):
        """Empty paint layer that the second-pass paint-over fills."""
        self.layer("brushwork", "paint")

    def dump_over(self, sizes, threshold=7, **kw):
        """Print the paint-over op alone, for a second `klad apply` batch.

        paint-over reads the composed drawing, so it must run after the main
        ops land. It paints unifying strokes onto the `brushwork` layer, taking
        colour from the figure layers below, which keeps the sky untouched.
        """
        print(json.dumps({"op": "paintover", "layer": "brushwork",
                          "from": self.paint_layers, "sizes": list(sizes),
                          "threshold": threshold, "seed": self.seed(), **kw}))


def sky(card, accent, horizon=0.62):
    """A deep dusk sky painted with soft nebula drifts, a glow, and stars.

    The gradient base and glow are vector, but the nebula is scumbled on with a
    soft brush and the stars vary in size and softness, so the background does
    not read as a flat SVG wash behind the painted figure.
    """
    card.layer("sky", "vector")
    card.node("sky", {"type": "rect", "x": 0, "y": 0, "w": CARD_W, "h": CARD_H,
                      "fill": linear(0, 0, 0, CARD_H,
                                     [[0, SKY_TOP], [horizon, "#15123a"],
                                      [1, SKY_LOW]])})
    card.node("sky", {"type": "ellipse", "cx": CARD_W / 2, "cy": CARD_H * horizon,
                      "rx": CARD_W, "ry": CARD_H * 0.5,
                      "fill": radial(CARD_W / 2, CARD_H * horizon, CARD_W,
                                     [[0, accent + "33"], [0.5, accent + "11"],
                                      [1, accent + "00"]])})
    # Scumbled nebula clouds painted with a soft brush over the gradient.
    card.layer("nebula", "paint", opacity=0.6)
    rng = _Rng(13)
    tints = [accent, "#6a4fd0", "#3f6fd0", "#b85aa0"]
    for i in range(14):
        x = rng.next() * CARD_W
        y = rng.next() * CARD_H * (horizon + 0.25)
        size = 150 + rng.next() * 260
        tint = tints[i % len(tints)]
        card.op({"op": "stroke", "layer": "nebula", "brush": "soft",
                 "size": size, "color": tint + "26", "flow": 0.5,
                 "path": f"M{x:.0f} {y:.0f} l{rng.next() * 120 - 60:.0f} "
                         f"{rng.next() * 80 - 40:.0f}", "seed": card.seed()})
    # Stars: most tiny and soft, a few brighter with a faint bloom.
    card.layer("stars", "vector", blend="screen")
    rng = _Rng(97)
    for _ in range(120):
        x = rng.next() * CARD_W
        y = rng.next() * CARD_H * (horizon + 0.2)
        r = 0.5 + rng.next() * 2.0
        a = int(70 + rng.next() * 150)
        blur = 0.4 if rng.next() < 0.75 else 2.2
        card.node("stars", {"type": "ellipse", "cx": x, "cy": y, "rx": r, "ry": r,
                            "fill": STAR + f"{a:02x}", "blur": blur})


def card_frame(card, number, title, accent):
    """The caption band, the keyline border, and the two lines of type."""
    card.layer("frame", "vector")
    band_top = CARD_H - 150
    card.node("frame", {"type": "rect", "x": 0, "y": band_top - 48,
                        "w": CARD_W, "h": CARD_H - (band_top - 48),
                        "fill": linear(0, band_top - 48, 0, CARD_H,
                                       [[0, "#07060f00"], [0.35, "#07060fcc"],
                                        [1, "#07060ff5"]])})
    card.node("frame", {"type": "rect", "x": 24, "y": 24, "w": CARD_W - 48,
                        "h": CARD_H - 48, "radius": 20, "fill": "none",
                        "stroke": {"paint": accent + "aa", "width": 2.5}})
    card.node("frame", {"type": "text", "text": number, "font": "Share Tech Mono",
                        "size": 23, "x": CARD_W / 2, "y": band_top - 6,
                        "align": "center", "tracking": 7, "fill": accent})
    card.node("frame", {"type": "text", "text": title, "font": "Orbitron Bold",
                        "size": 48, "x": CARD_W / 2, "y": band_top + 34,
                        "align": "center", "tracking": 9, "fill": "#f4f0ff"})
