#!/usr/bin/env python3
"""Tests for DRC report classification."""

from __future__ import annotations

import unittest

import run_drc


def finding(category: str, message: str, severity: str) -> str:
    return (
        f"[{category}]: {message}\n"
        "    Local override; "
        f"Severity: {severity}\n"
        "    @(1.0000 mm, 2.0000 mm): test item\n"
    )


class DrcReportTest(unittest.TestCase):
    def test_relaxed_board_rule_is_release_blocking(self):
        board = run_drc.pcbnew.LoadBoard(str(run_drc.BOARD_PATH))
        board.GetDesignSettings().m_MinClearance = run_drc.pcbnew.FromMM(0.05)
        errors = run_drc.board_contract_errors(board)
        self.assertTrue(any("copper clearance" in error for error in errors))

    def test_missing_global_library_is_not_release_blocking(self):
        report = finding(
            "lib_footprint_issues",
            "The current configuration does not include the library 'Resistor_SMD'.",
            "warning",
        )
        tally, severities, blocking = run_drc.parse_drc_findings(report)
        self.assertEqual(tally["lib_footprint_issues"], 1)
        self.assertEqual(severities[("warning", "lib_footprint_issues")], 1)
        self.assertEqual(blocking, 0)

    def test_footprint_library_drift_is_release_blocking(self):
        report = finding(
            "lib_footprint_issues",
            "Footprint R1 does not match the copy in its library.",
            "warning",
        )
        _, _, blocking = run_drc.parse_drc_findings(report)
        self.assertEqual(blocking, 1)

    def test_dangling_copper_warning_is_release_blocking(self):
        report = finding("track_dangling", "Track has a dangling end.", "warning")
        _, _, blocking = run_drc.parse_drc_findings(report)
        self.assertEqual(blocking, 1)


if __name__ == "__main__":
    unittest.main()
