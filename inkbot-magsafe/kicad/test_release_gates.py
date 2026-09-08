#!/usr/bin/env python3
"""Tests for evidence-backed fabrication release gates."""

from __future__ import annotations

import json
import os
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import layout_route
import release_gates


class ReleaseGateTest(unittest.TestCase):
    def write(self, data: dict) -> Path:
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        path = Path(directory.name) / "gates.json"
        path.write_text(json.dumps(data))
        return path

    def document(self, classification: str = "EVT") -> dict:
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

    def test_repository_evt_blocks_production_fabrication(self):
        with mock.patch.dict(os.environ, {"INKBOT_PRODUCTION_EXPORT": "1"}):
            with self.assertRaisesRegex(SystemExit, "production fabrication export blocked"):
                layout_route.export_fab()

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
        path = self.write(document)
        report = path.parent / "reports" / "schematic-review.pdf"
        report.parent.mkdir()
        report.write_bytes(b"independent review")
        summary = release_gates.validate_release_gates(path)
        self.assertTrue(summary.production_releasable)
        self.assertEqual(summary.blocked, ())
        self.assertEqual(summary.evidence_files, (report,))

    def test_missing_evidence_file_is_rejected(self):
        document = self.document()
        document["gates"][0]["evidence"] = ["reports/missing.pdf"]
        with self.assertRaisesRegex(ValueError, "does not exist"):
            release_gates.validate_release_gates(self.write(document))

    def test_evidence_path_cannot_escape_release_directory(self):
        document = self.document()
        document["gates"][0]["evidence"] = ["../outside.pdf"]
        path = self.write(document)
        with self.assertRaisesRegex(ValueError, "escapes the release directory"):
            release_gates.validate_release_gates(path)


if __name__ == "__main__":
    unittest.main()
