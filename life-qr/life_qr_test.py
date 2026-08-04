#!/usr/bin/env python3
"""Tests for the Life QR stacking model (QR roof, time toward the bed)."""

from __future__ import annotations

import unittest

try:
    import segno
except ImportError:  # pragma: no cover
    segno = None


def step(cells: list[int], w: int, h: int) -> list[int]:
    out = []
    for y in range(h):
        for x in range(w):
            n = 0
            for dy in (-1, 0, 1):
                for dx in (-1, 0, 1):
                    if dx == 0 and dy == 0:
                        continue
                    nx, ny = x + dx, y + dy
                    if 0 <= nx < w and 0 <= ny < h:
                        n += cells[ny * w + nx]
            a = cells[y * w + x]
            out.append(1 if (n == 3 or (a and n == 2)) else 0)
    return out


def pad(cells: list[int], w: int, h: int, margin: int) -> tuple[list[int], int, int]:
    nw, nh = w + 2 * margin, h + 2 * margin
    out = [0] * (nw * nh)
    for y in range(h):
        for x in range(w):
            out[(y + margin) * nw + (x + margin)] = cells[y * w + x]
    return out, nw, nh


def flip_rows(cells: list[int], w: int, h: int) -> list[int]:
    out = []
    for y in range(h - 1, -1, -1):
        out.extend(cells[y * w : (y + 1) * w])
    return out


def evolve(seed: list[int], w: int, h: int, generations: int) -> list[list[int]]:
    hist = [seed]
    cur = seed
    for _ in range(generations):
        cur = step(cur, w, h)
        hist.append(cur)
    return hist


def stack_for_print(history: list[list[int]]) -> list[list[int]]:
    """history[0]=QR roof → print stack[0]=base, stack[-1]=roof."""
    return list(reversed(history))


class StackingTests(unittest.TestCase):
    def test_downward_time_is_forward_life(self) -> None:
        # Tiny seed as a stand-in for a QR roof.
        seed = [
            0, 0, 0, 0, 0,
            0, 0, 1, 0, 0,
            0, 0, 0, 1, 0,
            0, 1, 1, 1, 0,
            0, 0, 0, 0, 0,
        ]
        w = h = 5
        gens = 6
        history = evolve(seed, w, h, gens)
        stack = stack_for_print(history)
        self.assertEqual(stack[-1], seed)
        self.assertEqual(len(stack), gens + 1)
        # below = step(above)
        for z in range(len(stack) - 1):
            self.assertEqual(
                step(stack[z + 1], w, h),
                stack[z],
                f"break between print layers {z + 1} (above) and {z} (below)",
            )

    def test_pad_and_flip(self) -> None:
        cells = [1, 0, 0, 0, 0, 1]
        # 2x3
        flipped = flip_rows(cells, 3, 2)
        self.assertEqual(flipped, [0, 0, 1, 1, 0, 0])
        padded, nw, nh = pad(flipped, 3, 2, 1)
        self.assertEqual((nw, nh), (5, 4))
        self.assertEqual(padded[1 * 5 + 1], 0)
        self.assertEqual(padded[1 * 5 + 3], 1)


@unittest.skipUnless(segno is not None, "segno not installed")
class QrRoofTests(unittest.TestCase):
    def test_segno_roof_stack_consistent(self) -> None:
        qr = segno.make("HELLO", error="M", mask=0)
        matrix = [list(row) for row in qr.matrix]
        h = len(matrix)
        w = len(matrix[0])
        self.assertEqual(w, h)
        cells = [1 if matrix[y][x] else 0 for y in range(h) for x in range(w)]
        cells = flip_rows(cells, w, h)
        cells, w, h = pad(cells, w, h, margin=4 + 2)
        history = evolve(cells, w, h, generations=8)
        stack = stack_for_print(history)
        self.assertEqual(stack[-1], history[0])
        for z in range(len(stack) - 1):
            self.assertEqual(step(stack[z + 1], w, h), stack[z])
        # Roof still has finder density.
        roof = history[0]
        live = sum(roof)
        self.assertGreater(live, 50)

    def test_finder_corners_present(self) -> None:
        qr = segno.make("HI", error="M", mask=0)
        m = qr.matrix
        # Top-left finder outer corners live.
        self.assertTrue(m[0][0] and m[0][6] and m[6][0] and m[6][6])
        self.assertFalse(m[1][1])
        # Dark module.
        n = len(m)
        self.assertTrue(m[n - 8][8])


class PillarTests(unittest.TestCase):
    def test_augment_below(self) -> None:
        # above has an island; below empty → pillar
        above = [0, 1, 0, 0, 0, 0, 0, 0, 0]
        below = [0] * 9
        out = [
            below[i] if below[i] else (2 if above[i] else 0) for i in range(9)
        ]
        self.assertEqual(out[1], 2)
        self.assertEqual(sum(1 for v in out if v == 2), 1)


if __name__ == "__main__":
    unittest.main()
