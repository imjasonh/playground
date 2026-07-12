#!/usr/bin/env python3
"""Generate a frequency-2 spherical pentakis snub dodecahedron.

Construction
------------
1. Build a snub dodecahedron (Archimedean solid U29).
2. Kis the 12 pentagons: add each pentagon's center, raise it to the
   circumsphere, replace the pentagon with 5 triangles
   → pentakis snub dodecahedron (140 triangles).
3. Frequency-2 subdivide every triangle (connect edge midpoints → 4
   triangles each) and project all vertices onto the circumsphere
   → 560 triangles.

Writes:
  geodesic.scad  – OpenSCAD polyhedron
  geodesic.stl   – ASCII STL
"""

from __future__ import annotations

import math
from collections import Counter
from pathlib import Path

import numpy as np

OUT_DIR = Path(__file__).resolve().parent
RADIUS = 50.0  # output mesh circumradius


# ---------------------------------------------------------------------------
# Snub dodecahedron vertices (alternation / qfbox A,B,C form, edge length 2)
# ---------------------------------------------------------------------------

def _poly_root(poly, lo: float, hi: float) -> float:
    for _ in range(120):
        mid = 0.5 * (lo + hi)
        if poly(lo) * poly(mid) <= 0:
            hi = mid
        else:
            lo = mid
    return 0.5 * (lo + hi)


def snub_dodecahedron_vertices() -> np.ndarray:
    """Return 60 vertices of one enantiomorph, centered at the origin."""
    phi = (1.0 + math.sqrt(5.0)) / 2.0

    def pA(a: float) -> float:
        a2 = a * a
        return a2**3 - 4 * phi**2 * a2**2 + (20 * phi + 13) * a2 - phi**6

    def pB(b: float) -> float:
        b2 = b * b
        return b2**3 - 5 * phi**2 * b2**2 + 7 * phi**4 * b2 - phi**4

    def pC(c: float) -> float:
        c2 = c * c
        return c2**3 + (4 * phi + 1) * c2**2 + 4 * phi**4 * c2 - phi**6

    A = _poly_root(pA, 0.6, 0.7)
    B = _poly_root(pB, 0.3, 0.4)
    C = _poly_root(pC, 0.7, 0.8)

    prototypes = [
        np.array([-A, C, (A * phi + 2 * B + C) * phi]),
        np.array([-B, (A + B) * phi**2 + C, A + (B + C) * phi]),
        np.array([A + B * phi, B + C, (A + B) * phi**2 + C * phi]),
        np.array([A * phi + B, A * phi + B * phi**2 + C, (A + B + C) * phi]),
        np.array([-(A + B) * phi, A * phi + B + C, (A + C) * phi + B * phi**2]),
    ]

    verts: list[np.ndarray] = []
    seen: set[tuple[float, float, float]] = set()

    def add(v: np.ndarray) -> None:
        key = (round(float(v[0]), 10), round(float(v[1]), 10), round(float(v[2]), 10))
        if key not in seen:
            seen.add(key)
            verts.append(v.copy())

    for p in prototypes:
        x, y, z = float(p[0]), float(p[1]), float(p[2])
        for ep in ((x, y, z), (z, x, y), (y, z, x)):
            ex, ey, ez = ep
            for es in (
                (ex, ey, ez),
                (-ex, -ey, ez),
                (-ex, ey, -ez),
                (ex, -ey, -ez),
            ):
                add(np.array(es, dtype=float))

    arr = np.array(verts, dtype=float)
    if len(arr) != 60:
        raise RuntimeError(f"expected 60 snub vertices, got {len(arr)}")
    arr -= arr.mean(axis=0)
    return arr


def scale_to_unit_edge(verts: np.ndarray) -> tuple[np.ndarray, float]:
    """Scale so nearest-neighbor distance is 1. Returns (verts, edge)."""
    dmin = None
    n = len(verts)
    for i in range(n):
        for j in range(i + 1, n):
            d = float(np.linalg.norm(verts[i] - verts[j]))
            if dmin is None or d < dmin:
                dmin = d
    assert dmin is not None and dmin > 0
    return verts / dmin, 1.0


# ---------------------------------------------------------------------------
# Faces via unit-edge graph + azimuth walk
# ---------------------------------------------------------------------------

def adjacency(verts: np.ndarray, edge: float = 1.0, tol: float = 1e-4):
    n = len(verts)
    adj = [[] for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            d = float(np.linalg.norm(verts[i] - verts[j]))
            if abs(d - edge) < tol:
                adj[i].append(j)
                adj[j].append(i)
    for i, nbrs in enumerate(adj):
        if len(nbrs) != 5:
            raise RuntimeError(f"vertex {i} degree {len(nbrs)}, expected 5")
    return adj


def _azimuth(verts: np.ndarray, v: int, w: int) -> float:
    radial = verts[v] / np.linalg.norm(verts[v])
    vec = verts[w] - verts[v]
    vec = vec - radial * np.dot(vec, radial)
    tmp = np.array([1.0, 0.0, 0.0]) if abs(radial[0]) < 0.9 else np.array([0.0, 1.0, 0.0])
    e1 = np.cross(radial, tmp)
    e1 /= np.linalg.norm(e1)
    e2 = np.cross(radial, e1)
    return math.atan2(float(np.dot(vec, e2)), float(np.dot(vec, e1)))


def find_faces(verts: np.ndarray, adj):
    """Return unique triangle and pentagon faces (outward CCW)."""

    def next_face_vertex(u: int, v: int) -> int:
        nbrs = list(adj[v])
        nbrs.sort(key=lambda w: _azimuth(verts, v, w))
        return nbrs[(nbrs.index(u) + 1) % len(nbrs)]

    used: set[tuple[int, int]] = set()
    faces: list[tuple[int, ...]] = []
    n = len(verts)
    for u0 in range(n):
        for v0 in adj[u0]:
            if (u0, v0) in used:
                continue
            face = [u0, v0]
            u, v = u0, v0
            used.add((u, v))
            for _ in range(10):
                w = next_face_vertex(u, v)
                used.add((v, w))
                if w == u0:
                    break
                face.append(w)
                u, v = v, w
            else:
                raise RuntimeError(f"face walk exploded: {face}")
            cyc = tuple(face)
            v0_, v1, v2 = verts[cyc[0]], verts[cyc[1]], verts[cyc[2]]
            if np.dot(v0_, np.cross(v1 - v0_, v2 - v0_)) < 0:
                cyc = tuple(reversed(cyc))
            faces.append(cyc)

    # Deduplicate (walk yields each face once, but keep safe)
    uniq = {}
    for f in faces:
        uniq[frozenset(f)] = f
    faces = list(uniq.values())
    counts = Counter(len(f) for f in faces)
    if counts.get(3) != 80 or counts.get(5) != 12:
        raise RuntimeError(f"unexpected face counts: {counts}")
    triangles = [f for f in faces if len(f) == 3]
    pentagons = [f for f in faces if len(f) == 5]
    return triangles, pentagons


# ---------------------------------------------------------------------------
# Kis pentagons → project to sphere → frequency-2 subdivide
# ---------------------------------------------------------------------------

def _orient(verts, tri):
    a, b, c = tri
    v0, v1, v2 = verts[a], verts[b], verts[c]
    if np.dot(v0, np.cross(v1 - v0, v2 - v0)) < 0:
        return (a, c, b)
    return tri


def pentakis_on_sphere(verts: np.ndarray, triangles, pentagons):
    R = float(np.mean(np.linalg.norm(verts, axis=1)))
    verts = [v.copy() for v in verts]
    new_tris = [tuple(t) for t in triangles]

    for pent in pentagons:
        center = np.mean([verts[i] for i in pent], axis=0)
        center = center / np.linalg.norm(center) * R
        idx = len(verts)
        verts.append(center)
        for k in range(5):
            a = pent[k]
            b = pent[(k + 1) % 5]
            new_tris.append(_orient(verts, (idx, a, b)))

    return np.array(verts, dtype=float), new_tris


def frequency2_on_sphere(verts: np.ndarray, tris):
    R = float(np.mean(np.linalg.norm(verts, axis=1)))
    verts = [v / np.linalg.norm(v) * R for v in verts]
    edge_mid: dict[tuple[int, int], int] = {}

    def midpoint(i: int, j: int) -> int:
        key = (i, j) if i < j else (j, i)
        if key in edge_mid:
            return edge_mid[key]
        m = 0.5 * (verts[i] + verts[j])
        m = m / np.linalg.norm(m) * R
        idx = len(verts)
        verts.append(m)
        edge_mid[key] = idx
        return idx

    out = []
    for a, b, c in tris:
        ab = midpoint(a, b)
        bc = midpoint(b, c)
        ca = midpoint(c, a)
        for tri in ((a, ab, ca), (b, bc, ab), (c, ca, bc), (ab, bc, ca)):
            out.append(_orient(verts, tri))

    return np.array(verts, dtype=float), out


# ---------------------------------------------------------------------------
# Exporters
# ---------------------------------------------------------------------------

def write_stl_ascii(path: Path, verts: np.ndarray, faces) -> None:
    lines = ["solid geodesic"]
    for a, b, c in faces:
        v0, v1, v2 = verts[a], verts[b], verts[c]
        n = np.cross(v1 - v0, v2 - v0)
        nn = np.linalg.norm(n)
        if nn > 0:
            n = n / nn
        lines.append(f"  facet normal {n[0]:.8e} {n[1]:.8e} {n[2]:.8e}")
        lines.append("    outer loop")
        for v in (v0, v1, v2):
            lines.append(f"      vertex {v[0]:.8e} {v[1]:.8e} {v[2]:.8e}")
        lines.append("    endloop")
        lines.append("  endfacet")
    lines.append("endsolid geodesic")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_scad(path: Path, verts: np.ndarray, faces) -> None:
    pts = ",\n    ".join(f"[{v[0]:.8f}, {v[1]:.8f}, {v[2]:.8f}]" for v in verts)
    fcs = ",\n    ".join(f"[{a}, {b}, {c}]" for a, b, c in faces)
    text = f"""// Frequency-2 spherical pentakis snub dodecahedron
// 560 triangles on a sphere of radius {RADIUS:g}.
// Generated by generate.py — regenerate rather than editing by hand.
//
// Construction:
//   1. snub dodecahedron
//   2. kis pentagons, apexes on circumsphere  (140 tris)
//   3. frequency-2 midpoint split + spherical projection  (560 tris)

geodesic();

module geodesic() {{
  polyhedron(
    points = [
    {pts}
    ],
    faces = [
    {fcs}
    ],
    convexity = 10
  );
}}
"""
    path.write_text(text, encoding="utf-8")


def main() -> None:
    verts = snub_dodecahedron_vertices()
    verts, edge = scale_to_unit_edge(verts)
    adj = adjacency(verts, edge=edge)
    triangles, pentagons = find_faces(verts, adj)
    print(
        f"snub dodecahedron: {len(verts)} verts, "
        f"{len(triangles)} tris, {len(pentagons)} pents"
    )

    verts, tris140 = pentakis_on_sphere(verts, triangles, pentagons)
    print(f"pentakis: {len(verts)} verts, {len(tris140)} tris")
    if len(tris140) != 140:
        raise RuntimeError(f"expected 140 tris, got {len(tris140)}")

    verts, tris560 = frequency2_on_sphere(verts, tris140)
    print(f"freq-2: {len(verts)} verts, {len(tris560)} tris")
    if len(tris560) != 560:
        raise RuntimeError(f"expected 560 tris, got {len(tris560)}")

    R = float(np.mean(np.linalg.norm(verts, axis=1)))
    verts = verts * (RADIUS / R)

    stl_path = OUT_DIR / "geodesic.stl"
    scad_path = OUT_DIR / "geodesic.scad"
    write_stl_ascii(stl_path, verts, tris560)
    write_scad(scad_path, verts, tris560)
    print(f"wrote {stl_path} ({stl_path.stat().st_size} bytes)")
    print(f"wrote {scad_path} ({scad_path.stat().st_size} bytes)")


if __name__ == "__main__":
    main()
