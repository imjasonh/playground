#!/usr/bin/env python3
"""Run KiCad's real DRC engine on the board and summarize the report.

KiCad 8+ exposes DRC on the command line:

    kicad-cli pcb drc --format report --output fab/drc-report.txt inkbot-magsafe.kicad_pcb

This environment ships KiCad 7.0, whose `kicad-cli pcb` only exports Gerbers.
The same DRC engine is still reachable through the pcbnew Python API via
``WriteDRCReport``, which runs clearance, hole, keepout, courtyard, mask,
edge, connectivity, and silk checks and writes a full report. This script runs
it, writes ``fab/drc-report.txt``, prints a per-category tally, and exits
non-zero when any error-severity violation remains.

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


def main() -> int:
    if not BOARD_PATH.exists():
        print(f"missing board: {BOARD_PATH}", file=sys.stderr)
        return 2

    OUT.parent.mkdir(parents=True, exist_ok=True)
    board = pcbnew.LoadBoard(str(BOARD_PATH))
    board.BuildConnectivity()
    # aReportAllTrackErrors=True so every clearance instance is listed.
    pcbnew.WriteDRCReport(board, str(OUT), pcbnew.EDA_UNITS_MILLIMETRES, True)

    text = OUT.read_text()
    tally = Counter(re.findall(r"^\[([a-z_]+)\]", text, re.MULTILINE))
    severities = Counter()
    lines = text.splitlines()
    for index, line in enumerate(lines):
        match = re.match(r"^\[([a-z_]+)\]", line)
        if match is None:
            continue
        category = match.group(1)
        detail = "\n".join(lines[index + 1:index + 4])
        severity = re.search(r"Severity: (error|warning|ignore)", detail)
        severities[(severity.group(1) if severity else "unknown", category)] += 1

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
    print(f"Warnings: {warnings}")
    return 1 if errors > 0 or unconnected > 0 else 0


if __name__ == "__main__":
    raise SystemExit(main())
