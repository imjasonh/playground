/** Axial neighbor order for pointy-top hexes, matching redblobgames corners. */
export const HEX_DIRS = [
  { q: 1, r: 0 },
  { q: 1, r: -1 },
  { q: 0, r: -1 },
  { q: -1, r: 0 },
  { q: -1, r: 1 },
  { q: 0, r: 1 },
];

export function mod6(index) {
  return ((index % 6) + 6) % 6;
}

export function hexKey(q, r) {
  return `${q},${r}`;
}

export function hexAdd(a, b) {
  return { q: a.q + b.q, r: a.r + b.r };
}

export function hexDistance(a, b) {
  const dq = a.q - b.q;
  const dr = a.r - b.r;
  return (Math.abs(dq) + Math.abs(dr) + Math.abs(dq + dr)) / 2;
}

export function hexCountInRadius(radius) {
  return 1 + 3 * radius * (radius + 1);
}

export function hexesInRadius(radius) {
  const cells = [];
  for (let q = -radius; q <= radius; q += 1) {
    const rMin = Math.max(-radius, -q - radius);
    const rMax = Math.min(radius, -q + radius);
    for (let r = rMin; r <= rMax; r += 1) {
      cells.push({ q, r });
    }
  }
  return cells;
}

export function hexRound(q, r) {
  let x = q;
  let z = r;
  let y = -x - z;
  let rx = Math.round(x);
  let ry = Math.round(y);
  let rz = Math.round(z);
  const dx = Math.abs(rx - x);
  const dy = Math.abs(ry - y);
  const dz = Math.abs(rz - z);
  if (dx > dy && dx > dz) {
    rx = -ry - rz;
  } else if (dy > dz) {
    ry = -rx - rz;
  } else {
    rz = -rx - ry;
  }
  return { q: rx, r: rz };
}

export function hexLine(a, b) {
  const n = hexDistance(a, b);
  if (n === 0) {
    return [{ q: a.q, r: a.r }];
  }
  const out = [];
  for (let i = 0; i <= n; i += 1) {
    const t = i / n;
    out.push(hexRound(a.q + (b.q - a.q) * t, a.r + (b.r - a.r) * t));
  }
  return out;
}

/**
 * Stable id for the grid vertex at corner `vertexIndex` of hex (q, r).
 * The same meeting point from any of the three hexes that share it
 * produces the same string.
 */
export function vertexId(q, r, vertexIndex) {
  const i = mod6(vertexIndex);
  const neighA = HEX_DIRS[i];
  const neighB = HEX_DIRS[(i + 1) % 6];
  const hexes = [
    [q, r],
    [q + neighA.q, r + neighA.r],
    [q + neighB.q, r + neighB.r],
  ];
  hexes.sort((left, right) => {
    if (left[0] !== right[0]) {
      return left[0] - right[0];
    }
    return left[1] - right[1];
  });
  return `${hexes[0][0]},${hexes[0][1]}|${hexes[1][0]},${hexes[1][1]}|${hexes[2][0]},${hexes[2][1]}`;
}

export function axialToWorld(q, r, size) {
  return {
    x: size * Math.sqrt(3) * (q + r / 2),
    z: size * 1.5 * r,
  };
}

export function hexCornerWorld(q, r, vertexIndex, size) {
  const center = axialToWorld(q, r, size);
  const i = mod6(vertexIndex);
  const angle = ((60 * i - 30) * Math.PI) / 180;
  return {
    x: center.x + size * Math.cos(angle),
    z: center.z + size * Math.sin(angle),
  };
}

/**
 * Neighbor across the edge between vertex `edgeIndex` and the next vertex.
 */
export function edgeNeighbor(q, r, edgeIndex) {
  return hexAdd({ q, r }, HEX_DIRS[mod6(edgeIndex + 1)]);
}
