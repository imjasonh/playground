#!/usr/bin/env python3
"""Tests for evidence-backed fabrication release gates."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

import release_gates


class ReleaseGateTest(unittest.TestCase):
    def write(self, data: dict) -> Path:
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        path = Path(directory.name) / "gates.json"
        path.write_text(json.dumps(data))
        return path

    @staticmethod
    def document(classification: str = "EVT") -> dict:
        return {
            "schema_version": 1,
            "product": "inkbot-magsafe",
            "classification": classification,
            "gates": [
                {
                    "id": "schematic-review",
                    "status": "blocked",
                    "evidence": [],
                }
            ],
        }

    def test_repository_gate_file_is_valid_and_blocked(self):
        summary = release_gates.validate_release_gates()
        self.assertEqual(summary.classification, "EVT")
        self.assertFalse(summary.production_releasable)
        self.assertGreater(len(summary.blocked), 0)

    def test_passed_gate_requires_evidence(self):
        document = self.document()
        document["gates"][0]["status"] = "passed"
        with self.assertRaisesRegex(ValueError, "requires evidence"):
            release_gates.validate_release_gates(self.write(document))

    def test_production_cannot_contain_blocked_gate(self):
        with self.assertRaisesRegex(ValueError, "cannot contain blocked"):
            release_gates.validate_release_gates(self.write(self.document("PRODUCTION")))

    def test_duplicate_ids_are_rejected(self):
        document = self.document()
        document["gates"].append(document["gates"][0].copy())
        with self.assertRaisesRegex(ValueError, "duplicate gate id"):
            release_gates.validate_release_gates(self.write(document))

    def test_evidence_backed_production_gate_is_releasable(self):
        document = self.document("PRODUCTION")
        document["gates"][0]["status"] = "passed"
        document["gates"][0]["evidence"] = ["reports/schematic-review.pdf"]
        summary = release_gates.validate_release_gates(self.write(document))
        self.assertTrue(summary.production_releasable)
        self.assertEqual(summary.blocked, ())


if __name__ == "__main__":
    unittest.main()
