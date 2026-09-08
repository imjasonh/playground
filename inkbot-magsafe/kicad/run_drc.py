#!/usr/bin/env python3
"""Run KiCad's real DRC engine on the board and summarize the report.

KiCad 8+ exposes DRC on the command line:

    kicad-cli pcb drc --format report --output fab/drc-report.txt inkbot-magsafe.kicad_pcb

This environment ships KiCad 7.0, whose `kicad-cli pcb` only exports Gerbers.
The same DRC engine is still reachable through the pcbnew Python API via
``WriteDRCReport``, which runs clearance, hole, keepout, courtyard, mask,
edge, connectivity, and silk checks and writes a full report. This script runs
it, writes ``fab/drc-report.txt``, prints a per-category tally, and exits
nonzero for errors, open connections, or release-blocking geometry warnings.

Usage:
  python3 run_drc.py
"""

from __future__ import annotations

import re
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, "/usr/lib/python3/dist-packages")
import pcbnew  # noqa: E402

HERE = Path(__file__).resolve().parent
BOARD_PATH = HERE / "inkbot-magsafe.kicad_pcb"
OUT = HERE / "fab" / "drc-report.txt"
BLOCKING_WARNING_CATEGORIES = {
    "connection_width",
    "isolated_copper",
    "track_dangling",
    "via_dangling",
}


def release_blocking_warning(category: str, heading: str) -> bool:
    """Return whether a DRC warning blocks fabrication release."""
    return category in BLOCKING_WARNING_CATEGORIES or (
        category == "lib_footprint_issues"
        and "current configuration does not include the library" not in heading
    )


def board_contract_errors(board: pcbnew.BOARD) -> list[str]:
    """Return violations of manufacturing rules that DRC cannot infer."""
    errors = []
    settings = board.GetDesignSettings()
    expected_minimums = {
        "copper-to-edge clearance": (settings.m_CopperEdgeClearance, 0.5),
        "copper clearance": (settings.m_MinClearance, 0.1),
        "track width": (settings.m_TrackMinWidth, 0.1),
        "hole clearance": (settings.m_HoleClearance, 0.2),
        "hole-to-hole clearance": (settings.m_HoleToHoleMin, 0.2),
        "through-hole drill": (settings.m_MinThroughDrill, 0.2),
        "via diameter": (settings.m_ViasMinSize, 0.45),
        "via annular width": (settings.m_ViasMinAnnularWidth, 0.1),
    }
    for name, (actual, expected) in expected_minimums.items():
        actual_mm = pcbnew.ToMM(actual)
        if actual_mm + 1e-9 < expected:
            errors.append(f"{name} is {actual_mm:.3f} mm, expected at least {expected:.3f} mm")

    if board.GetCopperLayerCount() != 4:
        errors.append(f"board has {board.GetCopperLayerCount()} copper layers, expected 4")
    thickness_mm = pcbnew.ToMM(settings.GetBoardThickness())
    if abs(thickness_mm - 0.8) > 1e-9:
        errors.append(f"board thickness is {thickness_mm:.3f} mm, expected 0.800 mm")
    if not settings.m_HasStackup:
        errors.append("board has no explicit stackup")

    edge_bounds = board.GetBoardEdgesBoundingBox()
    edge_size = (
        round(pcbnew.ToMM(edge_bounds.GetWidth()), 3),
        round(pcbnew.ToMM(edge_bounds.GetHeight()), 3),
    )
    if edge_size != (60.05, 99.05):
        errors.append(f"board edge bounds are {edge_size[0]} x {edge_size[1]} mm")

    rule_areas = set()
    planes = set()
    for zone in board.Zones():
        if zone.GetIsRuleArea():
            bounds = zone.GetBoundingBox()
            rule_areas.add(
                (
                    round(pcbnew.ToMM(bounds.GetX()), 3),
                    round(pcbnew.ToMM(bounds.GetY()), 3),
                    round(pcbnew.ToMM(bounds.GetWidth()), 3),
                    round(pcbnew.ToMM(bounds.GetHeight()), 3),
                    zone.GetLayer(),
                    zone.GetDoNotAllowTracks(),
                    zone.GetDoNotAllowVias(),
                    zone.GetDoNotAllowCopperPour(),
                )
            )
        else:
            planes.add((zone.GetLayer(), zone.GetNetname()))

    expected_rule_areas = {
        (0.0, 83.0, 4.25, 12.0, -1, True, True, True),
        (12.5, 58.0, 35.0, 24.0, -1, True, True, True),
        (3.0, 3.0, 54.0, 54.0, -1, True, True, True),
    }
    missing_rule_areas = expected_rule_areas - rule_areas
    for area in sorted(missing_rule_areas):
        errors.append(f"missing required copper keepout {area[:4]}")

    expected_planes = {
        (pcbnew.In1_Cu, "/SYS"),
        (pcbnew.In2_Cu, "GND"),
    }
    for layer, net in sorted(expected_planes - planes):
        errors.append(f"missing {board.GetLayerName(layer)} plane for {net}")
    return errors


def parse_drc_findings(text: str) -> tuple[Counter, Counter, int]:
    """Return category, severity, and release-blocking warning counts."""
    tally = Counter(re.findall(r"^\[([a-z_]+)\]", text, re.MULTILINE))
    severities = Counter()
    blocking_warnings = 0
    lines = text.splitlines()
    for index, line in enumerate(lines):
        match = re.match(r"^\[([a-z_]+)\]", line)
        if match is None:
            continue
        category = match.group(1)
        detail = "\n".join(lines[index + 1:index + 4])
        severity = re.search(r"Severity: (error|warning|ignore)", detail)
        level = severity.group(1) if severity else "unknown"
        severities[(level, category)] += 1
        if level == "warning" and release_blocking_warning(category, line):
            blocking_warnings += 1
    return tally, severities, blocking_warnings


def main() -> int:
    if not BOARD_PATH.exists():
        print(f"missing board: {BOARD_PATH}", file=sys.stderr)
        return 2

    OUT.parent.mkdir(parents=True, exist_ok=True)
    board = pcbnew.LoadBoard(str(BOARD_PATH))
    board.BuildConnectivity()
    contract_errors = board_contract_errors(board)
    # aReportAllTrackErrors=True so every clearance instance is listed.
    pcbnew.WriteDRCReport(board, str(OUT), pcbnew.EDA_UNITS_MILLIMETRES, True)

    text = OUT.read_text()
    tally, severities, blocking_warnings = parse_drc_findings(text)

    total = 0
    m = re.search(r"Found (\d+) DRC violations", text)
    if m:
        total = int(m.group(1))
    unconnected = 0
    mu = re.search(r"Found (\d+) unconnected pads", text)
    if mu:
        unconnected = int(mu.group(1))

    print(f"DRC report: {OUT}")
    print(f"  violations: {total}  (+{unconnected} unconnected pads)")
    print("  by category:")
    for cat, n in tally.most_common():
        print(f"    {n:5d}  {cat}")

    errors = sum(
        count
        for (severity, category), count in severities.items()
        if severity == "error" and category != "unconnected_items"
    )
    warnings = sum(
        count for (severity, _category), count in severities.items()
        if severity == "warning"
    )
    print(f"\nHard violations (excluding open ratsnest): {errors}")
    print(f"Warnings: {warnings} ({blocking_warnings} release-blocking)")
    print(f"Board contract violations: {len(contract_errors)}")
    for error in contract_errors:
        print(f"  {error}")
    return (
        1
        if errors > 0 or unconnected > 0 or blocking_warnings > 0 or contract_errors
        else 0
    )


if __name__ == "__main__":
    raise SystemExit(main())
