"""Shared drawing kit for the First Contact triptych.

Each card generator imports this module and prints klad `apply` ops as JSON
lines. A card is planned the way a painter plans a picture:

- One small light (a glowing sprout, a lit fingertip) is the key light. Every
  form takes its colour from that lamp: bright near it, falling off with
  distance, and turning into a cool violet shadow on the side facing away.
- A rose rim light from the ringed planet and a dim blue one from the sky pick
  out the edges that face them.
- Silhouettes are smooth curves through hand-placed points, and limbs and
  fingers are tapered tubes, so nothing is a rectangle or a circle unless the
  thing itself is one.

A figure is built from rigid pieces (head, arm, hand). Each piece is lit as a
smooth vector underpainting, then `klad paintover` repaints it as oil strokes
on a paint layer of its own. That paint layer is attached to a bone, so the
pieces can be posed and in-betweened for the animation.
"""

import json
import math
import os
import sys

CARD_W = 1024
CARD_H = 1280
# A panel's width plus the triptych gutter: panel n shows the panorama from
# n * PANEL_STEP, so the sky, the planet and its rings run across all three.
PANEL_STEP = 1064
HORIZON = 872
PLANET = (1576, 610, 440)

KEY = "#d6fff0"
AMBIENT = (0.24, 0.21, 0.38)
ROSE = "#ff8fbf"
SKYLIGHT = "#7d8fe6"

FRAMES = 48
FPS = 12

# SKETCH=1 leaves the paint layers empty, so a render of the first pass shows
# the underpaintings alone. That is the quick way to check the drawing.
SKETCH = os.environ.get("SKETCH") == "1"


# Colour arithmetic on 0..1 triples.

def rgb(color):
    if not isinstance(color, str):
        return tuple(color)
    h = color.lstrip("#")
    return tuple(int(h[i:i + 2], 16) / 255 for i in (0, 2, 4))


def hexc(color, alpha=None):
    c = [max(0.0, min(1.0, v)) for v in rgb(color)]
    out = "#" + "".join(f"{round(v * 255):02x}" for v in c)
    if alpha is not None:
        out += f"{round(max(0.0, min(1.0, alpha)) * 255):02x}"
    return out


def mix(a, b, t):
    a, b = rgb(a), rgb(b)
    return tuple(x + (y - x) * t for x, y in zip(a, b))


def mul(a, b):
    return tuple(x * y for x, y in zip(rgb(a), rgb(b)))


def scale(a, k):
    return tuple(x * k for x in rgb(a))


def add(a, b):
    return tuple(x + y for x, y in zip(rgb(a), rgb(b)))


def linear(x1, y1, x2, y2, stops):
    return {"linear": {"from": [x1, y1], "to": [x2, y2], "stops": stops}}


def radial(cx, cy, r, stops):
    return {"radial": {"center": [cx, cy], "radius": r, "stops": stops}}


class Rng:
    """A tiny deterministic generator, so a seed always draws the same card."""

    def __init__(self, seed):
        self.state = (seed * 2654435761 + 12345) & 0xFFFFFFFF

    def next(self):
        self.state = (self.state * 1103515245 + 12345) & 0x7FFFFFFF
        return self.state / 0x7FFFFFFF

    def span(self, lo, hi):
        return lo + (hi - lo) * self.next()


# Geometry: dense point lists, so shapes can be moved, measured and lit.

def _catmull(p0, p1, p2, p3, t):
    t2, t3 = t * t, t * t * t
    return tuple(
        0.5 * (2 * b + (c - a) * t + (2 * a - 5 * b + 4 * c - d) * t2
               + (3 * b - a - 3 * c + d) * t3)
        for a, b, c, d in zip(p0, p1, p2, p3))


def _run(pts, n):
    """An open Catmull-Rom curve through pts, n samples per span."""
    if len(pts) < 2:
        return list(pts)
    q = [pts[0]] + list(pts) + [pts[-1]]
    out = []
    for i in range(1, len(q) - 2):
        for k in range(n):
            out.append(_catmull(q[i - 1], q[i], q[i + 1], q[i + 2], k / n))
    out.append(pts[-1])
    return out


def smooth(points, closed=True, n=8):
    """A smooth curve through points. A third item on a point makes a corner."""
    pts = [(p[0], p[1]) for p in points]
    corners = [i for i, p in enumerate(points) if len(p) > 2]
    if not closed:
        cuts = [0] + [i for i in corners if 0 < i < len(pts) - 1] + [len(pts) - 1]
        out = []
        for a, b in zip(cuts, cuts[1:]):
            out += _run(pts[a:b + 1], n)[:-1]
        return out + [pts[-1]]
    if not corners:
        m = len(pts)
        out = []
        for i in range(m):
            for k in range(n):
                out.append(_catmull(pts[i - 1], pts[i], pts[(i + 1) % m],
                                    pts[(i + 2) % m], k / n))
        return out
    first = corners[0]
    pts = pts[first:] + pts[:first]
    cuts = [c - first for c in corners] + [len(pts)]
    ring = pts + [pts[0]]
    out = []
    for a, b in zip(cuts, cuts[1:]):
        out += _run(ring[a:b + 1], n)[:-1]
    return out


def _area(pts):
    return sum(a[0] * b[1] - b[0] * a[1]
               for a, b in zip(pts, pts[1:] + pts[:1])) / 2


class Shape:
    """One or more closed outlines, used as a silhouette."""

    def __init__(self, *parts):
        self.parts = []
        for part in parts:
            part = [(float(x), float(y)) for x, y in part]
            if _area(part) < 0:
                part.reverse()
            self.parts.append(part)

    def __add__(self, other):
        return Shape(*(self.parts + other.parts))

    @property
    def d(self):
        return " ".join(
            "M" + " L".join(f"{x:.1f} {y:.1f}" for x, y in part) + " Z"
            for part in self.parts)

    @property
    def points(self):
        return [p for part in self.parts for p in part]

    @property
    def bbox(self):
        xs = [p[0] for p in self.points]
        ys = [p[1] for p in self.points]
        return min(xs), min(ys), max(xs), max(ys)

    @property
    def centre(self):
        x0, y0, x1, y1 = self.bbox
        return (x0 + x1) / 2, (y0 + y1) / 2

    def moved(self, dx, dy):
        return Shape(*[[(x + dx, y + dy) for x, y in part]
                       for part in self.parts])

    def turned(self, degrees, about):
        a = math.radians(degrees)
        ca, sa = math.cos(a), math.sin(a)
        ox, oy = about
        return Shape(*[[(ox + (x - ox) * ca - (y - oy) * sa,
                         oy + (x - ox) * sa + (y - oy) * ca)
                        for x, y in part] for part in self.parts])

    def grown(self, k, about=None):
        ox, oy = about or self.centre
        return Shape(*[[(ox + (x - ox) * k, oy + (y - oy) * k)
                        for x, y in part] for part in self.parts])


def blob(points, n=8):
    """A closed silhouette through points (x, y) or corner points (x, y, 1)."""
    return Shape(smooth(points, closed=True, n=n))


def ellipse(cx, cy, rx, ry, turn=0, n=72):
    a = math.radians(turn)
    ca, sa = math.cos(a), math.sin(a)
    pts = []
    for i in range(n):
        t = 2 * math.pi * i / n
        x, y = rx * math.cos(t), ry * math.sin(t)
        pts.append((cx + x * ca - y * sa, cy + x * sa + y * ca))
    return Shape(pts)


def tube(points, radii, n=10):
    """A limb, finger, cable or stem: a tapered tube along a smooth centre line."""
    line = smooth(points, closed=False, n=n)
    spans = len(points) - 1
    rad = []
    for i in range(len(line)):
        u = min(i / n, spans - 1e-9)
        k = int(u)
        t = u - k
        t = t * t * (3 - 2 * t)
        rad.append(radii[k] + (radii[k + 1] - radii[k]) * t)
    left, right = [], []
    for i, (x, y) in enumerate(line):
        ax, ay = line[max(i - 1, 0)]
        bx, by = line[min(i + 1, len(line) - 1)]
        tx, ty = bx - ax, by - ay
        length = math.hypot(tx, ty) or 1.0
        nx, ny = -ty / length, tx / length
        left.append((x + nx * rad[i], y + ny * rad[i]))
        right.append((x - nx * rad[i], y - ny * rad[i]))

    def cap(centre, start, r):
        a0 = math.atan2(start[1] - centre[1], start[0] - centre[0])
        return [(centre[0] + r * math.cos(a0 - math.pi * k / 8),
                 centre[1] + r * math.sin(a0 - math.pi * k / 8))
                for k in range(1, 8)]

    outline = (left + cap(line[-1], left[-1], rad[-1]) + right[::-1]
               + cap(line[0], right[0], rad[0]))
    return Shape(outline)


def curve(points, n=8):
    """An open smooth path, as SVG path data, for seams, folds and wires."""
    pts = smooth(points, closed=False, n=n)
    return "M" + " L".join(f"{x:.1f} {y:.1f}" for x, y in pts)


# Vector nodes for underpaintings.

def _d(shape):
    return shape.d if isinstance(shape, Shape) else shape


def area(shape, fill, blur=0, opacity=1, **extra):
    node = {"type": "path", "d": _d(shape), "fill": fill, **extra}
    if blur:
        node["blur"] = blur
    if opacity != 1:
        node["opacity"] = opacity
    return node


def line(d, color, width, blur=0, opacity=1, **extra):
    node = {"type": "path", "d": d, "fill": "none",
            "stroke": {"paint": color, "width": width, "cap": "round",
                       "join": "round"}, **extra}
    if blur:
        node["blur"] = blur
    if opacity != 1:
        node["opacity"] = opacity
    return node


def spot(cx, cy, rx, ry, fill, blur=0, opacity=1, **extra):
    node = {"type": "ellipse", "cx": cx, "cy": cy, "rx": rx, "ry": ry,
            "fill": fill, **extra}
    if blur:
        node["blur"] = blur
    if opacity != 1:
        node["opacity"] = opacity
    return node


def halo(cx, cy, r, color, strength=1.0):
    """A light's glow: opaque in the middle, gone at the radius."""
    return spot(cx, cy, r, r, radial(cx, cy, r, [
        [0, hexc(color, strength)], [0.25, hexc(color, strength * 0.45)],
        [0.6, hexc(color, strength * 0.12)], [1, hexc(color, 0)]]))


def cast(shape, dx, dy, blur, opacity=0.5):
    """The shadow one form throws on the form under it."""
    return area(shape.moved(dx, dy), "#080616", blur=blur, opacity=opacity)


def clipped(shape, children):
    return {"type": "group", "clip": _d(shape), "children": list(children)}


def edge_band(shape, toward, width, power=1.6):
    """The strip along a silhouette's edge that faces a light.

    `toward(x, y)` gives the unit direction to the light from that point and
    how strong it is there. The strip is as wide as the edge faces the light,
    so it tapers away where the surface turns from it.
    """
    runs = []
    for part in shape.parts:
        m = len(part)
        rows = []
        for i, (x, y) in enumerate(part):
            ax, ay = part[i - 1]
            bx, by = part[(i + 1) % m]
            tx, ty = bx - ax, by - ay
            length = math.hypot(tx, ty) or 1.0
            nx, ny = ty / length, -tx / length
            lx, ly, gain = toward(x, y)
            w = max(0.0, nx * lx + ny * ly) ** power * gain
            rows.append((x, y, nx, ny, w))
        start = next((i for i, r in enumerate(rows) if r[4] <= 0.04), None)
        if start is None:
            start = 0
        rows = rows[start:] + rows[:start]
        run = []
        for row in rows + [(0, 0, 0, 0, 0)]:
            if row[4] > 0.04:
                run.append(row)
            elif run:
                if len(run) > 2:
                    runs.append(run)
                run = []
    out = []
    for run in runs:
        outer = [(x + nx * 1.5, y + ny * 1.5) for x, y, nx, ny, w in run]
        inner = [(x - nx * width * w, y - ny * width * w)
                 for x, y, nx, ny, w in run]
        out.append("M" + " L".join(f"{x:.1f} {y:.1f}"
                                   for x, y in outer + inner[::-1]) + " Z")
    return " ".join(out)


class Piece:
    def __init__(self, name, bone, sizes, threshold, focus, relief):
        self.name = name
        self.under = "u-" + name
        self.bone = bone
        self.sizes = sizes
        self.threshold = threshold
        self.focus = focus
        self.relief = relief


class Card:
    """Collects the apply ops of one card, in the batches klad needs."""

    def __init__(self, panel, lamp, reach=380, power=1.0, key=KEY, rims=()):
        self.panel = panel
        self.ox = panel * PANEL_STEP
        self.lamp = lamp
        self.reach = reach
        self.power = power
        self.keylight = rgb(key)
        self.rims = list(rims)
        self.main = []
        self.overs = []
        self.late = []
        self.pieces = []
        self.rigged = []
        self.follow = []
        self.bones = []
        self.keys = {}
        self.cur = None
        self._seed = 0
        self.op({"op": "timeline", "frames": FRAMES, "fps": FPS})

    def op(self, obj):
        self.main.append(obj)
        return obj

    def seed(self):
        self._seed += 1
        return self._seed

    def layer(self, lid, kind, **extra):
        self.op({"op": "add",
                 "layer": {"id": lid, "kind": kind, "name": lid, **extra}})

    def node(self, layer, node):
        self.op({"op": "add", "node": node, "in": layer})

    # Light.

    def glow(self, x, y, gain=1.0):
        """How much of the key light reaches a point."""
        r = math.hypot(x - self.lamp[0], y - self.lamp[1])
        return self.power * gain / (1 + (r / self.reach) ** 2)

    def shade(self, albedo):
        return mul(albedo, AMBIENT)

    def lit(self, albedo, x, y, gain=1.0):
        return add(self.shade(albedo),
                   scale(mul(albedo, self.keylight), self.glow(x, y, gain)))

    def _lamp_fill(self, albedo, gain):
        stops = []
        reach_out = 1500
        for r in (0, 50, 110, 180, 260, 360, 480, 640, 860, 1150, 1500):
            k = self.power * gain / (1 + (r / self.reach) ** 2)
            c = add(self.shade(albedo), scale(mul(albedo, self.keylight), k))
            stops.append([r / reach_out, hexc(c)])
        return radial(self.lamp[0], self.lamp[1], reach_out, stops)

    def _to_lamp(self, x, y):
        dx, dy = self.lamp[0] - x, self.lamp[1] - y
        length = math.hypot(dx, dy) or 1.0
        return dx / length, dy / length, min(1.0, self.glow(x, y, 2.2))

    # Pieces.

    def piece(self, name, bone=None, sizes=(26, 13, 6, 3), threshold=4,
              focus=None, relief=1.3):
        """Start a rigid piece: an underpainting and the paint layer over it."""
        p = Piece(name, bone, list(sizes), threshold, focus, relief)
        self.layer(p.under, "vector")
        effects = []
        if relief:
            effects = [{"relief": {"light": [-0.6, -0.75], "strength": relief,
                                   "softness": 2.6, "highlight": "#fff4e6"}}]
        self.layer(name, "paint", effects=effects)
        self.pieces.append(p)
        self.cur = p
        return p

    def form(self, shape, albedo, depth=None, soft=None, gain=1.0, away=None,
             edge=0.7, rim=1.0, under=(), extra=(), over=(), flat=False):
        """Light one form of the current piece and add it to the underpainting.

        The base is the lamp's light falling off with distance. A copy of the
        silhouette moved away from the lamp and blurred is the form shadow, so
        the lit part is the crescent that faces the lamp. `extra` nodes
        (seams, decals, cast shadows) go over that, then the edge lights.
        """
        p = self.cur
        x0, y0, x1, y1 = shape.bbox
        cx, cy = shape.centre
        size = min(x1 - x0, y1 - y0)
        if depth is None:
            depth = max(6.0, 0.45 * size)
        if soft is None:
            soft = max(2.0, depth * 0.5)
        if away is None:
            dx, dy = cx - self.lamp[0], cy - self.lamp[1]
            length = math.hypot(dx, dy) or 1.0
            away = (dx / length, dy / length)
        dark = self.shade(albedo)
        pad = 40
        kids = [{"type": "rect", "x": x0 - pad, "y": y0 - pad,
                 "w": x1 - x0 + 2 * pad, "h": y1 - y0 + 2 * pad,
                 "fill": self._lamp_fill(albedo, gain)}]
        kids += list(under)
        if not flat:
            kids.append(area(shape.moved(away[0] * depth, away[1] * depth),
                             hexc(dark), blur=soft, opacity=0.94))
        kids += list(extra)
        if edge:
            band = edge_band(shape, self._to_lamp, max(3.0, min(14.0, size * 0.1)))
            if band:
                near = min(shape.points, key=lambda p: math.hypot(
                    p[0] - self.lamp[0], p[1] - self.lamp[1]))
                bright = self.lit(albedo, near[0], near[1], 1.5 * gain)
                kids.append(area(band, hexc(bright), blur=1.6, opacity=edge))
        for rx, ry, color, width, strength in self.rims:
            if not rim:
                break
            band = edge_band(shape, lambda x, y: (rx, ry, 1.0),
                             min(width, max(2.5, size * 0.09)), 3.0)
            if band:
                tint = mix(mul(albedo, color), color, 0.35)
                kids.append(area(band, hexc(tint), blur=1.4,
                                 opacity=min(1.0, strength * rim)))
        kids += list(over)
        self.node(p.under, clipped(shape, kids))
        # A middle value, so a gap between strokes doesn't read as a fleck.
        self.fill(shape, mix(dark, self.lit(albedo, cx, cy, gain), 0.5))

    def fill(self, shape, color):
        """Block in a silhouette on the current paint layer.

        The paint-over then covers this flat colour, and the layer's locked
        alpha keeps its strokes inside the silhouette.
        """
        if SKETCH:
            return
        for part in shape.parts:
            self.op({"op": "fill", "layer": self.cur.name,
                     "polygon": [[round(x, 1), round(y, 1)] for x, y in part],
                     "color": hexc(color)})

    def close(self):
        """End the current piece: lock its silhouette and plan its paint-over."""
        p = self.cur
        self.op({"op": "set", "id": p.name, "lockAlpha": True})
        over = {"op": "paintover", "layer": p.name, "from": [p.under],
                "sizes": p.sizes, "threshold": p.threshold, "brush": "oil",
                "vary": 0.014, "curve": 0.8, "seed": self.seed()}
        if p.focus:
            over["focus"] = p.focus
        self.overs.append(over)
        self.late.append({"op": "set", "id": p.name, "lockAlpha": False})
        self.late.append({"op": "set", "id": p.under, "visible": False})
        if p.bone:
            self.rigged.append((p.name, p.bone))
        self.cur = None

    def light_layer(self, name, bone=None, blend="screen", opacity=1.0):
        """A vector layer for glows; with a bone, it follows that bone."""
        self.layer(name, "vector", blend=blend, opacity=opacity)
        if bone:
            self.follow.append((name, bone))

    # Rig and animation.

    def skeleton(self, bones):
        """Add the bones: (name, parent, head, tail) with parents first.

        The bundle gets a klad bones layer with each painted piece attached
        to its bone, so the figure can be posed by hand in the editor. The
        idle loop itself comes from `animate`.
        """
        self.bones = list(bones)
        self.layer("bones", "bones")
        for name, parent, head, tail in bones:
            op = {"op": "bone", "layer": "bones", "add": name,
                  "head": list(head), "tail": list(tail)}
            if parent:
                op["parent"] = parent
            self.late.append(op)

    def animate(self, motion):
        """Key every rigged piece through the loop from its bone's motion.

        `motion(t)` takes the loop's phase, 0 to 1, and returns the turn of
        each bone in degrees (clockwise, from the rest pose) and the root's
        offset. The turns go down the chain as they do on a skeleton: a hand
        follows its arm. klad in-betweens a posed bone by drawing every stroke
        again for every frame, which takes minutes for a painted piece, so
        the loop moves each piece's layer with keys instead. A key turns a
        layer about the middle of the canvas, so the offset that puts the
        bone's head where the chain carries it goes into the key's x and y.
        """
        cx, cy = CARD_W / 2, CARD_H / 2
        for frame in range(FRAMES):
            turns, root = motion(frame / FRAMES)
            world = {None: (0.0, root[0], root[1])}
            for name, parent, head, _ in self.bones:
                turn, tx, ty = world[parent]
                own = turns.get(name, 0.0)
                hx, hy = _turn(head, own)
                dx, dy = _turn((head[0] - hx, head[1] - hy), turn)
                world[name] = (turn + own, dx + tx, dy + ty)
            for layer, bone in self.rigged + self.follow:
                turn, tx, ty = world[bone]
                rx, ry = _turn((cx, cy), turn)
                self.key(layer, frame, ease="linear", rotate=round(turn, 3),
                         x=round(tx - cx + rx, 2), y=round(ty - cy + ry, 2))

    def key(self, target, frame, ease="in-out", **values):
        """Set key values; calls for one target and frame merge into one key."""
        slot = self.keys.setdefault((target, frame), {"ease": ease})
        slot.update(values)

    def pulse(self, target, low, high, period=FRAMES, phase=0.0):
        """Key an opacity that breathes, in a whole number of cycles a loop."""
        cycles = max(1, round(FRAMES / period))
        for frame in range(FRAMES):
            t = (frame / FRAMES * cycles + phase) * 2 * math.pi
            value = low + (high - low) * (0.5 + 0.5 * math.cos(t))
            self.key(target, frame, ease="linear", opacity=round(value, 3))

    # Output.

    def batches(self):
        late = list(self.late)
        late += [{"op": "attach", "layer": layer, "bone": bone}
                 for layer, bone in self.rigged]
        late += [{"op": "key", "id": target, "frame": frame, **values}
                 for (target, frame), values in self.keys.items()]
        late.append({"op": "clip", "add": "idle", "from": 0,
                     "to": FRAMES - 1, "loop": True})
        return [self.main] + [[o] for o in self.overs] + [late]

    def run(self, argv=None):
        argv = sys.argv if argv is None else argv
        batches = self.batches()
        if "--passes" in argv:
            sys.stdout.write(f"{len(batches)}\n")
        else:
            index = int(argv[argv.index("--pass") + 1]) if "--pass" in argv else 0
            sys.stdout.write(
                "".join(json.dumps(o) + "\n" for o in batches[index]))


def _turn(point, degrees):
    a = math.radians(degrees)
    ca, sa = math.cos(a), math.sin(a)
    return point[0] * ca - point[1] * sa, point[0] * sa + point[1] * ca


def wave(t, cycles=1, phase=0.0):
    """A sine through the loop: `cycles` whole swings, `phase` in turns."""
    return math.sin(2 * math.pi * (t * cycles + phase))


# The panorama behind all three panels.

def backdrop(card):
    """Dusk over a wet plain, with a ringed planet behind the middle panel."""
    ox = card.ox
    under, paint = "u-sky", "sky"
    card.layer(under, "vector")
    card.node(under, {"type": "rect", "x": 0, "y": 0, "w": CARD_W, "h": HORIZON + 4,
                      "fill": linear(0, 0, 0, HORIZON, [
                          [0, "#04051a"], [0.3, "#0b0d33"], [0.58, "#231950"],
                          [0.8, "#52296b"], [0.93, "#9a4d72"], [1, "#e09a86"]])})
    px, py, pr = PLANET[0] - ox, PLANET[1], PLANET[2]
    disc = ellipse(px, py, pr, pr, n=120)
    card.node(under, halo(px, py, pr * 1.45, "#c0508f", 0.5))
    tilt = 9
    bands = []
    rng = Rng(5)
    for i in range(11):
        y = py - pr + (i + 0.5) * 2 * pr / 11 + rng.span(-14, 14)
        tone = ["#e79ab0", "#6d2b6e", "#f0b6b4", "#8a3a7a"][i % 4]
        bands.append(area(ellipse(px, y, pr * 1.2, rng.span(10, 30), tilt),
                          tone, blur=rng.span(8, 18),
                          opacity=rng.span(0.16, 0.34)))
    card.node(under, clipped(disc, [
        {"type": "rect", "x": px - pr, "y": py - pr, "w": 2 * pr, "h": 2 * pr,
         "fill": radial(px - pr * 0.25, py + pr * 0.45, pr * 1.6, [
             [0, "#e58aa6"], [0.35, "#b9558a"], [0.7, "#6c2c72"],
             [1, "#2c1650"]])},
        *bands,
        area(ellipse(px + pr * 0.42, py - pr * 0.5, pr * 0.9, pr * 0.9),
             "#160a36", blur=90, opacity=0.6),
    ]))
    limb = edge_band(disc, lambda x, y: (-0.35, 0.94, 1.0), 16, 1.2)
    card.node(under, area(limb, "#ffb9cf", blur=7, opacity=0.6))
    # Haze sits on the horizon and swallows the planet's lower limb.
    card.node(under, {"type": "rect", "x": 0, "y": HORIZON - 260, "w": CARD_W,
                      "h": 264, "fill": linear(0, HORIZON - 260, 0, HORIZON + 4, [
                          [0, "#d9828800"], [0.6, "#d9828855"],
                          [1, "#f0b094ee"]])})
    # Far mesas, pale with distance.
    rng = Rng(11)
    x = -200.0
    while x < 3 * PANEL_STEP:
        w = rng.span(120, 420)
        h = rng.span(10, 46)
        gap = rng.span(60, 520)
        if x + w > ox - 50 and x < ox + CARD_W + 50 and rng.next() < 0.8:
            a = x - ox
            card.node(under, area(blob([
                (a, HORIZON + 4), (a + w * 0.08, HORIZON - h * 0.7),
                (a + w * 0.3, HORIZON - h), (a + w * 0.62, HORIZON - h * 0.86),
                (a + w * 0.9, HORIZON - h * 0.5), (a + w, HORIZON + 4)]),
                "#8a4a70", blur=1.5))
        x += w + gap
    # The plain: wet, so it carries the sky's glow near the horizon.
    card.node(under, {"type": "rect", "x": 0, "y": HORIZON, "w": CARD_W,
                      "h": CARD_H - HORIZON,
                      "fill": linear(0, HORIZON, 0, CARD_H, [
                          [0, "#b06a7c"], [0.06, "#6c3a62"], [0.3, "#2e1c44"],
                          [0.7, "#150e26"], [1, "#0b0818"]])})
    rng = Rng(23 + card.panel)
    for _ in range(16):
        y = HORIZON + 6 + rng.next() ** 2 * 230
        w = rng.span(80, 380) * (0.4 + (y - HORIZON) / 200)
        cx = rng.span(-60, CARD_W + 60)
        card.node(under, spot(cx, y, w, rng.span(1.5, 4) + (y - HORIZON) / 60,
                              "#e7a0a0", blur=3,
                              opacity=rng.span(0.08, 0.3)))
    card.node(under, spot(px, HORIZON + 80, pr * 0.7, 70, "#c9608a", blur=40,
                          opacity=0.25))
    card.layer(paint, "paint", effects=[{"relief": {
        "light": [-0.6, -0.75], "strength": 1.3, "softness": 4}}])
    card.overs.append({"op": "paintover", "layer": paint, "from": [under],
                       "sizes": [64, 30, 14], "threshold": 5, "brush": "oil",
                       "vary": 0.012, "curve": 0.6, "seed": 3})
    # Rings and stars are thin light, so they stay crisp over the brushwork.
    card.layer("rings", "vector", blend="screen")
    rng = Rng(31)
    a = math.radians(tilt)
    ca, sa = math.cos(a), math.sin(a)
    bands = []
    rr = pr * 1.4
    while rr < pr * 2.2:
        width = rng.span(1.5, 6)
        alpha = rng.span(0.05, 0.3)
        # A gap in the rings, as a moon would sweep one.
        if not pr * 1.78 < rr < pr * 1.86:
            bands.append((rr, width, alpha))
        rr += width + rng.span(1, 8)
    for half, tmin in (("back", math.pi), ("front", 0.0)):
        kids = []
        for k, (rr, width, alpha) in enumerate(bands):
            pts = []
            for i in range(61):
                t = tmin + math.pi * i / 60
                x, y = rr * math.cos(t), rr * 0.11 * math.sin(t)
                pts.append((px + x * ca - y * sa, py + x * sa + y * ca))
            kids.append(line("M" + " L".join(f"{x:.1f} {y:.1f}" for x, y in pts),
                             ["#f3c4c8", "#e9a9c4", "#ffdccf"][k % 3], width,
                             blur=0.8,
                             opacity=alpha * (0.5 if half == "back" else 0.8)))
        group = {"type": "group", "children": kids}
        if half == "back":
            # The far side of the rings passes behind the planet.
            hole = ellipse(px, py, pr + 2, pr + 2, n=120).parts[0][::-1]
            frame = [(-200, -200), (CARD_W + 200, -200),
                     (CARD_W + 200, CARD_H + 200), (-200, CARD_H + 200)]
            group["clip"] = ("M" + " L".join(f"{x:.1f} {y:.1f}" for x, y in frame)
                             + " Z M" + " L".join(f"{x:.1f} {y:.1f}"
                                                 for x, y in hole) + " Z")
        card.node("rings", group)
    card.layer("stars", "vector", blend="screen")
    rng = Rng(97 + card.panel * 7)
    for i in range(150):
        x = rng.span(0, CARD_W)
        y = rng.next() ** 1.7 * (HORIZON - 240)
        r = 0.6 + rng.next() ** 3 * 2.2
        if math.hypot(x - px, y - py) < pr + 8:
            continue
        fade = 1 - y / (HORIZON - 200)
        tint = ["#cfe6ff", "#ffe9d6", "#ffffff"][i % 3]
        star = spot(x, y, r, r, hexc(tint, (0.35 + 0.6 * rng.next()) * fade),
                    blur=0.5 if r < 1.6 else 1.6, id=f"star{i}")
        card.node("stars", star)
        if r > 1.5:
            card.pulse(f"star{i}", 0.35, 1.0, period=rng.span(14, 30),
                       phase=rng.span(0, 12))


def motes(card, layer, centre, count, spread, color, seed=1, drift=(0, -26)):
    """Specks of light adrift near the lamp, keyed to rise and fade in a loop."""
    card.layer(layer, "vector", blend="screen")
    rng = Rng(seed)
    for i in range(count):
        a = rng.span(0, 2 * math.pi)
        d = spread * rng.next() ** 0.7
        x = centre[0] + math.cos(a) * d
        y = centre[1] + math.sin(a) * d * 0.8
        r = rng.span(1.2, 3.4)
        nid = f"{layer}{i}"
        card.node(layer, spot(x, y, r * 2.6, r * 2.6, radial(x, y, r * 2.6, [
            [0, "#ffffff"], [0.35, hexc(color, 0.8)], [1, hexc(color, 0)]]),
            id=nid))
        start = rng.span(0, FRAMES)
        sway = rng.span(-12, 12)
        for frame in range(FRAMES):
            t = ((frame - start) % FRAMES) / FRAMES
            alpha = math.sin(math.pi * t) ** 1.5
            card.key(nid, frame, ease="linear",
                     x=round(sway * math.sin(2 * math.pi * t) + drift[0] * t, 1),
                     y=round(drift[1] * t, 1), opacity=round(alpha, 3))


def card_frame(card, number, title, accent):
    """The caption band, the keyline border, and the two lines of type."""
    card.layer("frame", "vector")
    band_top = CARD_H - 150
    card.node("frame", {"type": "rect", "x": 0, "y": band_top - 60,
                        "w": CARD_W, "h": CARD_H - (band_top - 60),
                        "fill": linear(0, band_top - 60, 0, CARD_H,
                                       [[0, "#07060f00"], [0.4, "#07060fd0"],
                                        [1, "#07060ff8"]])})
    card.node("frame", {"type": "rect", "x": 24, "y": 24, "w": CARD_W - 48,
                        "h": CARD_H - 48, "radius": 20, "fill": "none",
                        "stroke": {"paint": accent + "99", "width": 2.5}})
    card.node("frame", {"type": "text", "text": number, "font": "Share Tech Mono",
                        "size": 23, "x": CARD_W / 2, "y": band_top - 6,
                        "align": "center", "tracking": 7, "fill": accent})
    card.node("frame", {"type": "text", "text": title, "font": "Orbitron Bold",
                        "size": 48, "x": CARD_W / 2, "y": band_top + 34,
                        "align": "center", "tracking": 9, "fill": "#f4f0ff"})
