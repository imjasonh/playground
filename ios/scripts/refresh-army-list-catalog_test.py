#!/usr/bin/env python3
"""Tests for army-list catalog refresh helpers (ordering / determinism)."""

from __future__ import annotations

import importlib.util
import pathlib
import sys
import unittest

SCRIPT = pathlib.Path(__file__).with_name("refresh-army-list-catalog.py")
SPEC = importlib.util.spec_from_file_location("refresh_army_list_catalog", SCRIPT)
assert SPEC and SPEC.loader
MOD = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MOD
SPEC.loader.exec_module(MOD)


class NormalizeKeywordsTests(unittest.TestCase):
    def test_faction_first_then_alphabetical(self) -> None:
        got = MOD.normalize_keywords(
            ["Leader", "Character", "Faction: Chaos Space Marines", "Infantry"],
            "Chaos Space Marines",
        )
        self.assertEqual(
            got,
            [
                "Faction: Chaos Space Marines",
                "Character",
                "Infantry",
                "Leader",
            ],
        )

    def test_idempotent(self) -> None:
        once = MOD.normalize_keywords(
            ["Infantry", "Battleline", "Faction: Tyranids"],
            "Tyranids",
        )
        twice = MOD.normalize_keywords(once, "Tyranids")
        self.assertEqual(once, twice)

    def test_inserts_missing_faction_keyword(self) -> None:
        got = MOD.normalize_keywords(["Character", "Leader"], "Aeldari")
        self.assertEqual(got[0], "Faction: Aeldari")
        self.assertEqual(got[1:], ["Character", "Leader"])

    def test_dedupes(self) -> None:
        got = MOD.normalize_keywords(
            ["Character", "Character", "Faction: Orks", "Faction: Orks"],
            "Orks",
        )
        self.assertEqual(got, ["Faction: Orks", "Character"])

    def test_character_leader_order_stable_across_input_shuffles(self) -> None:
        a = MOD.normalize_keywords(
            ["Faction: Chaos Space Marines", "Character", "Leader"],
            "Chaos Space Marines",
        )
        b = MOD.normalize_keywords(
            ["Leader", "Faction: Chaos Space Marines", "Character"],
            "Chaos Space Marines",
        )
        self.assertEqual(a, b)
        self.assertEqual(a.index("Character"), a.index("Leader") - 1)


if __name__ == "__main__":
    raise SystemExit(unittest.main())
