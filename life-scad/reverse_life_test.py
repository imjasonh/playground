#!/usr/bin/env python3
"""Tests for reverse_life.py — grid rules, targets, and reverse search."""

from __future__ import annotations

import unittest

import reverse_life as rl


class GridTests(unittest.TestCase):
    def test_blinker_oscillates(self) -> None:
        h = rl.parse_pattern(".#./.#./.#.")
        v = h.step()
        self.assertEqual(v.render(), "...\n###\n...")
        self.assertEqual(v.step(), h)

    def test_block_still_life(self) -> None:
        b = rl.parse_pattern("##/##")
        self.assertEqual(b.step(), b)

    def test_glider_translates(self) -> None:
        g = rl.parse_pattern(".#./..#/###").padded(3)
        g4 = g.step().step().step().step()
        # After 4 gens a glider moves +1,+1 in this orientation on a dead border.
        self.assertEqual(g4.live_count(), 5)
        self.assertNotEqual(g4, g)

    def test_seed_string_roundtrip(self) -> None:
        g = rl.parse_pattern(".#./..#/###")
        self.assertEqual(rl.parse_pattern(g.seed_string()), g)

    def test_pad_keeps_center(self) -> None:
        g = rl.parse_pattern("#").padded(2)
        self.assertEqual(g.width, 5)
        self.assertEqual(g.alive(2, 2), 1)
        self.assertEqual(g.live_count(), 1)


class TargetTests(unittest.TestCase):
    def test_text_life(self) -> None:
        g = rl.text_grid("LIFE")
        self.assertEqual(g.height, 7)
        self.assertEqual(g.width, 5 * 4 + 3)
        self.assertGreater(g.live_count(), 20)
        self.assertIn("#", g.render())

    def test_text_rejects_unknown(self) -> None:
        with self.assertRaises(ValueError):
            rl.text_grid("@")

    def test_presets_parse(self) -> None:
        for name, pat in rl.PRESETS.items():
            g = rl.parse_pattern(pat)
            self.assertGreaterEqual(g.live_count(), 1, name)

    def test_qr_size_and_finders(self) -> None:
        try:
            g = rl.qr_grid("HI")
        except rl.ReverseError:
            self.skipTest("segno not installed")
        self.assertEqual((g.width, g.height), (21, 21))
        self.assertEqual(g.alive(0, 0), 1)
        self.assertEqual(g.alive(6, 0), 1)
        self.assertEqual(g.alive(0, 6), 1)
        self.assertEqual(g.alive(3, 3), 1)
        self.assertEqual(g.alive(1, 1), 0)
        self.assertEqual(g.alive(7, 0), 0)
        self.assertEqual(g.alive(8, 6), 1)
        self.assertEqual(g.alive(9, 6), 0)
        self.assertEqual(g.alive(8, 13), 1)

    @unittest.skipUnless(rl.HAS_PYSAT, "python-sat not installed")
    def test_qr_needs_margin_for_predecessor(self) -> None:
        try:
            g = rl.qr_grid("HI")
        except rl.ReverseError:
            self.skipTest("segno not installed")
        # Tight board: Garden of Eden / unreachable.
        self.assertIsNone(rl._sat_best_predecessor(g, samples=1))
        # With margin, a predecessor exists.
        padded = g.padded(2)
        pred = rl._sat_best_predecessor(padded, samples=2)
        self.assertIsNotNone(pred)
        assert pred is not None
        self.assertEqual(pred.step(), padded)


class ReverseTests(unittest.TestCase):
    def test_still_life_tower(self) -> None:
        b = rl.parse_pattern("##/##").padded(2)
        hist = rl.reverse_history(b, generations=10, method="auto")
        self.assertEqual(len(hist), 11)
        self.assertEqual(hist[-1], b)
        for i in range(len(hist) - 1):
            self.assertEqual(hist[i].step(), hist[i + 1])

    def test_zero_generations(self) -> None:
        g = rl.parse_pattern("#")
        self.assertEqual(rl.reverse_history(g, 0), [g])

    @unittest.skipUnless(rl.HAS_PYSAT, "python-sat not installed")
    def test_blinker_maxsat_deep(self) -> None:
        b = rl.parse_pattern(".#./.#./.#.").padded(2)
        hist = rl.reverse_history(b, generations=16, method="maxsat")
        self.assertEqual(len(hist), 17)
        self.assertEqual(hist[-1], b)
        for i in range(len(hist) - 1):
            self.assertEqual(hist[i].step(), hist[i + 1])
        # Oscillator history should stay a blinker, not explode.
        self.assertEqual(hist[0].live_count(), 3)

    @unittest.skipUnless(rl.HAS_PYSAT, "python-sat not installed")
    def test_letter_maxsat_short(self) -> None:
        g = rl.text_grid("L").padded(3)
        hist = rl.reverse_history(g, generations=3, method="maxsat")
        self.assertEqual(hist[-1], g)
        for i in range(len(hist) - 1):
            self.assertEqual(hist[i].step(), hist[i + 1])

    @unittest.skipUnless(rl.HAS_PYSAT, "python-sat not installed")
    def test_forward_then_reverse_roundtrip(self) -> None:
        seed = rl.parse_pattern(".#./..#/###").padded(4)
        target = seed
        for _ in range(5):
            target = target.step()
        hist = rl.reverse_history(target, generations=5, method="maxsat")
        self.assertEqual(hist[-1], target)
        for i in range(len(hist) - 1):
            self.assertEqual(hist[i].step(), hist[i + 1])

    @unittest.skipUnless(rl.HAS_PYSAT, "python-sat not installed")
    def test_multigen_letter(self) -> None:
        g = rl.parse_pattern("#.../#.../#.../#.../####").padded(2)
        hist = rl.reverse_history(g, generations=3, method="multigen")
        self.assertEqual(hist[-1], g)
        for i in range(len(hist) - 1):
            self.assertEqual(hist[i].step(), hist[i + 1])

    def test_walksat_block(self) -> None:
        b = rl.parse_pattern("##/##").padded(1)
        # Still-life shortcut applies even under walksat.
        hist = rl.reverse_history(b, generations=4, method="walksat")
        self.assertEqual(hist[-1], b)
        self.assertTrue(all(g == b for g in hist))

    def test_cli_seed_string(self) -> None:
        rc = rl.main(["--preset", "block", "--generations", "4", "--margin", "2"])
        self.assertEqual(rc, 0)


if __name__ == "__main__":
    unittest.main()
