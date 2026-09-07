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
    tally = Counter(re.findall(r"\[([a-z_]+)\]", text))

    total = 0
    m = re.search(r"Found (\d+) DRC violations", text)
    if m:
        total = int(m.group(1))
    unconnected = 0
    mu = re.search(r"Found (\d+) unconnected pads", text)
    if mu:
        unconnected = int(mu.group(1))

    # lib_footprint_issues are library-table warnings from script-loaded
    # footprints, not board defects; call them out separately.
    lib_warn = tally.get("lib_footprint_issues", 0)

    print(f"DRC report: {OUT}")
    print(f"  violations: {total}  (+{unconnected} unconnected pads)")
    print("  by category:")
    for cat, n in tally.most_common():
        print(f"    {n:5d}  {cat}")

    hard = total - lib_warn
    print(f"\nHard violations (excluding lib_footprint_issues): {hard}")
    return 1 if hard > 0 or unconnected > 0 else 0


if __name__ == "__main__":
    raise SystemExit(main())
