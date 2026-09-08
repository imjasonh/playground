#!/usr/bin/env python3
"""Tests for evidence-backed fabrication release gates."""

from __future__ import annotations

import hashlib
import json
import os
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import layout_route
import release_gates

EVIDENCE_CONTENT = b"independent qualification report with raw measurements"


class ReleaseGateTest(unittest.TestCase):
    def write(self, data: dict) -> Path:
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        path = Path(directory.name) / "gates.json"
        path.write_text(json.dumps(data))
        return path

    def document(self, classification: str = "EVT") -> dict:
        return {
            "schema_version": 2,
            "product": "inkbot-magsafe",
            "classification": classification,
            "gates": [
                {
                    "id": gate_id,
                    "status": "blocked",
                    "evidence": [],
                }
                for gate_id in release_gates.REQUIRED_GATE_IDS
            ],
        }

    def evidence(self, gate_id: str, location: str = "reports/qualification.pdf") -> dict:
        return {
            "gate_id": gate_id,
            "location": location,
            "sha256": hashlib.sha256(EVIDENCE_CONTENT).hexdigest(),
            "bytes": len(EVIDENCE_CONTENT),
            "kind": "test-report",
            "issuer": "Example Qualification Lab",
            "issued_on": "2026-09-07",
            "hardware_revision": "0.8.0-EVT",
            "source_commit": "a" * 40,
            "result": "pass",
            "criteria": ["All gate-specific acceptance criteria passed."],
            "subjects": ["DUT-001", "DUT-002"],
            "approved_by": ["reviewer@example.com", "release@example.com"],
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

    def test_production_fabrication_requires_clean_source(self):
        summary = release_gates.GateSummary(
            classification="PRODUCTION",
            passed=("all-gates",),
            blocked=(),
            evidence_files=(),
            evidence_records=(),
        )
        with self.assertRaisesRegex(SystemExit, "requires a clean source tree"):
            layout_route.validate_export_request(summary, True, True)
        layout_route.validate_export_request(summary, True, False)
        layout_route.validate_export_request(summary, False, True)

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

    def test_missing_or_extra_gate_is_rejected(self):
        missing = self.document()
        missing["gates"].pop()
        with self.assertRaisesRegex(ValueError, "release gate set mismatch"):
            release_gates.validate_release_gates(self.write(missing))

        extra = self.document()
        extra["gates"].append(
            {"id": "unreviewed-shortcut", "status": "blocked", "evidence": []}
        )
        with self.assertRaisesRegex(ValueError, "release gate set mismatch"):
            release_gates.validate_release_gates(self.write(extra))

    def test_gate_order_is_fixed_for_reviewable_manifests(self):
        document = self.document()
        document["gates"][0], document["gates"][1] = (
            document["gates"][1],
            document["gates"][0],
        )
        with self.assertRaisesRegex(ValueError, "required order"):
            release_gates.validate_release_gates(self.write(document))

    def test_evidence_backed_production_gate_is_releasable(self):
        document = self.document("PRODUCTION")
        for gate in document["gates"]:
            gate["status"] = "passed"
            gate["evidence"] = [self.evidence(gate["id"])]
        path = self.write(document)
        report = path.parent / "reports" / "qualification.pdf"
        report.parent.mkdir()
        report.write_bytes(EVIDENCE_CONTENT)
        summary = release_gates.validate_release_gates(path)
        self.assertTrue(summary.production_releasable)
        self.assertEqual(summary.blocked, ())
        self.assertEqual(summary.evidence_files, (report,))
        self.assertEqual(len(summary.evidence_records), len(release_gates.REQUIRED_GATE_IDS))

    def test_missing_evidence_file_is_rejected(self):
        document = self.document()
        gate = document["gates"][0]
        gate["evidence"] = [self.evidence(gate["id"], "reports/missing.pdf")]
        with self.assertRaisesRegex(ValueError, "does not exist"):
            release_gates.validate_release_gates(self.write(document))

    def test_evidence_path_cannot_escape_release_directory(self):
        document = self.document()
        gate = document["gates"][0]
        gate["evidence"] = [self.evidence(gate["id"], "../outside.pdf")]
        path = self.write(document)
        with self.assertRaisesRegex(ValueError, "escapes the release directory"):
            release_gates.validate_release_gates(path)

    def test_evidence_digest_size_and_approvals_are_enforced(self):
        document = self.document()
        gate = document["gates"][0]
        evidence = self.evidence(gate["id"])
        gate["evidence"] = [evidence]
        path = self.write(document)
        report = path.parent / "reports" / "qualification.pdf"
        report.parent.mkdir()
        report.write_bytes(EVIDENCE_CONTENT)

        evidence["sha256"] = "0" * 64
        path.write_text(json.dumps(document))
        with self.assertRaisesRegex(ValueError, "SHA-256 does not match"):
            release_gates.validate_release_gates(path)
        evidence["sha256"] = hashlib.sha256(EVIDENCE_CONTENT).hexdigest()
        evidence["bytes"] = 1
        path.write_text(json.dumps(document))
        with self.assertRaisesRegex(ValueError, "at least 32 bytes"):
            release_gates.validate_release_gates(path)
        evidence["bytes"] = len(EVIDENCE_CONTENT)
        evidence["approved_by"] = ["only-one@example.com"]
        path.write_text(json.dumps(document))
        with self.assertRaisesRegex(ValueError, "two distinct approver"):
            release_gates.validate_release_gates(path)

    def test_restricted_external_evidence_requires_https_and_digest(self):
        document = self.document()
        gate = document["gates"][0]
        evidence = self.evidence(
            gate["id"],
            "https://lab.example.com/reports/restricted-123",
        )
        gate["evidence"] = [evidence]
        summary = release_gates.validate_release_gates(self.write(document))
        self.assertEqual(summary.evidence_files, ())
        self.assertEqual(summary.evidence_records[0].location, evidence["location"])

        evidence["location"] = "http://lab.example.com/reports/restricted-123"
        with self.assertRaisesRegex(ValueError, "HTTPS"):
            release_gates.validate_release_gates(self.write(document))


if __name__ == "__main__":
    unittest.main()
