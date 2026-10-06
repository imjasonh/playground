// Built-in line pictures. Coordinates use y up.
// Outlines are one closed stroke so traced pieces meet end to end.

function catmull(p0, p1, p2, p3, t) {
  const t2 = t * t;
  const t3 = t2 * t;
  return {
    x:
      0.5 *
      (2 * p1.x +
        (-p0.x + p2.x) * t +
        (2 * p0.x - 5 * p1.x + 4 * p2.x - p3.x) * t2 +
        (-p0.x + 3 * p1.x - 3 * p2.x + p3.x) * t3),
    y:
      0.5 *
      (2 * p1.y +
        (-p0.y + p2.y) * t +
        (2 * p0.y - 5 * p1.y + 4 * p2.y - p3.y) * t2 +
        (-p0.y + 3 * p1.y - 3 * p2.y + p3.y) * t3),
  };
}

function smooth(points, perSegment, closed) {
  const src = points.map(([x, y]) => ({ x, y }));
  const n = src.length;
  const out = [];
  const segments = closed ? n : n - 1;
  for (let i = 0; i < segments; i += 1) {
    const i0 = closed ? (i - 1 + n) % n : Math.max(0, i - 1);
    const i1 = closed ? i : i;
    const i2 = closed ? (i + 1) % n : Math.min(n - 1, i + 1);
    const i3 = closed ? (i + 2) % n : Math.min(n - 1, i + 2);
    for (let s = 0; s < perSegment; s += 1) {
      out.push(catmull(src[i0], src[i1], src[i2], src[i3], s / perSegment));
    }
  }
  const last = closed ? src[0] : src[n - 1];
  out.push({ x: last.x, y: last.y });
  return out;
}

function ellipse(cx, cy, rx, ry, count) {
  const pts = [];
  for (let i = 0; i <= count; i += 1) {
    const t = (i / count) * Math.PI * 2;
    pts.push({ x: cx + rx * Math.cos(t), y: cy + ry * Math.sin(t) });
  }
  return pts;
}

function dog() {
  const outline = smooth(
    [
      [-26, -36],
      [-12, -36],
      [-14, -8],
      [8, -12],
      [16, -6],
      [14, -36],
      [30, -36],
      [26, 2],
      [38, 16],
      [54, 12],
      [66, 18],
      [64, 28],
      [50, 34],
      [40, 30],
      [34, 50],
      [24, 32],
      [6, 26],
      [-18, 22],
      [-32, 12],
      [-48, 30],
      [-34, 6],
      [-30, -8],
    ],
    4,
    true,
  );
  return [outline, ellipse(48, 24, 2.2, 2.6, 10), ellipse(62, 22, 2.4, 2, 8)];
}

function cat() {
  const outline = smooth(
    [
      [-18, -34],
      [14, -34],
      [16, -6],
      [22, 12],
      [26, 24],
      [20, 34],
      [24, 54],
      [12, 36],
      [4, 56],
      [-6, 36],
      [-12, 26],
      [-20, 8],
      [-36, 22],
      [-28, -4],
      [-22, -18],
    ],
    4,
    true,
  );
  return [
    outline,
    ellipse(-2, 30, 1.8, 2.2, 8),
    ellipse(10, 32, 1.8, 2.2, 8),
    smooth(
      [
        [20, 22],
        [34, 24],
      ],
      2,
      false,
    ),
    smooth(
      [
        [20, 18],
        [34, 16],
      ],
      2,
      false,
    ),
  ];
}

function bird() {
  const outline = smooth(
    [
      [-36, 2],
      [-14, -2],
      [8, -4],
      [24, 4],
      [34, 12],
      [48, 14],
      [34, 20],
      [26, 30],
      [12, 26],
      [-6, 18],
      [-30, 10],
    ],
    4,
    true,
  );
  return [
    outline,
    smooth(
      [
        [4, 16],
        [18, 22],
        [8, 8],
      ],
      3,
      false,
    ),
    ellipse(28, 22, 1.8, 2, 8),
    smooth(
      [
        [18, -2],
        [16, -16],
        [22, -16],
      ],
      2,
      false,
    ),
  ];
}

function fish() {
  return [
    ellipse(6, 0, 28, 14, 28),
    smooth(
      [
        [-22, 8],
        [-40, 18],
        [-36, 0],
        [-40, -16],
        [-22, -8],
      ],
      3,
      false,
    ),
    smooth(
      [
        [8, 12],
        [2, 26],
        [-8, 14],
      ],
      3,
      false,
    ),
    ellipse(22, 4, 2.2, 2.4, 8),
  ];
}

function house() {
  return [
    smooth(
      [
        [-24, -28],
        [24, -28],
        [24, 8],
        [0, 32],
        [-24, 8],
      ],
      2,
      true,
    ),
    smooth(
      [
        [-8, -28],
        [-8, -4],
        [8, -4],
        [8, -28],
      ],
      2,
      false,
    ),
    smooth(
      [
        [-16, 2],
        [-16, 12],
        [-6, 12],
        [-6, 2],
      ],
      1,
      true,
    ),
    smooth(
      [
        [10, 20],
        [10, 32],
        [18, 32],
        [18, 14],
      ],
      1,
      false,
    ),
  ];
}

function heart() {
  const pts = [];
  for (let i = 0; i <= 64; i += 1) {
    const t = (i / 64) * Math.PI * 2;
    pts.push({
      x: 16 * Math.sin(t) ** 3,
      y: 13 * Math.cos(t) - 5 * Math.cos(2 * t) - 2 * Math.cos(3 * t) - Math.cos(4 * t),
    });
  }
  return [pts];
}

function flower() {
  const strokes = [ellipse(0, 0, 8, 8, 16)];
  for (let i = 0; i < 6; i += 1) {
    const angle = (i / 6) * Math.PI * 2;
    const c = Math.cos(angle);
    const s = Math.sin(angle);
    const petal = [];
    for (let k = 0; k <= 18; k += 1) {
      const t = (k / 18) * Math.PI * 2;
      const px = 7 * Math.cos(t);
      const py = 16 * Math.sin(t) + 24;
      petal.push({ x: px * c - py * s, y: px * s + py * c });
    }
    strokes.push(petal);
  }
  return strokes;
}

export const PICTURES = [
  { id: "dog", name: "Dog", strokes: dog() },
  { id: "cat", name: "Cat", strokes: cat() },
  { id: "bird", name: "Bird", strokes: bird() },
  { id: "fish", name: "Fish", strokes: fish() },
  { id: "house", name: "House", strokes: house() },
  { id: "heart", name: "Heart", strokes: heart() },
  { id: "flower", name: "Flower", strokes: flower() },
];

export function pictureById(id) {
  for (const picture of PICTURES) {
    if (picture.id === id) {
      return picture;
    }
  }
  return PICTURES[0];
}
