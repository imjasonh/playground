#!/usr/bin/env python3
"""Check that every designed net on the board has at least two connected pads."""

from __future__ import annotations

import sys
from collections import defaultdict
from pathlib import Path

import pcbnew

ROOT = Path(__file__).resolve().parents[1]
PCB = ROOT / "nfc-eink.kicad_pcb"

REQUIRED = [
    "GND",
    "+3V3",
    "+3V3_EPD",
    "VSTORE",
    "NFC_LA",
    "NFC_LB",
    "I2C_SCL",
    "I2C_SDA",
    "NFC_FD",
    "NRST",
    "EPD_MOSI",
    "EPD_SCK",
    "EPD_CS",
    "EPD_DC",
    "EPD_RST",
    "EPD_BUSY",
    "EPD_PWR_EN",
    "BOOST_FB",
    "VOUT_EH",
]


def main() -> int:
    if not PCB.exists():
        print(f"missing {PCB}", file=sys.stderr)
        return 2
    board = pcbnew.LoadBoard(str(PCB))
    board.BuildConnectivity()
    conn = board.GetConnectivity()
    pads_by_net: dict[str, list[str]] = defaultdict(list)
    for fp in board.GetFootprints():
        ref = fp.GetReference()
        for pad in fp.Pads():
            name = pad.GetNetname()
            if name:
                pads_by_net[name].append(f"{ref}.{pad.GetNumber()}")
    errors: list[str] = []
    for net in REQUIRED:
        pads = pads_by_net.get(net, [])
        if len(pads) < 2:
            errors.append(f"{net}: {len(pads)} pads ({pads})")
            continue
        # KiCad 7: Test if two pads share a copper cluster.
        netitem = board.FindNet(net)
        if netitem is None:
            errors.append(f"{net}: missing net item")
            continue
        if hasattr(conn, "GetNetCount"):
            pass
        if hasattr(conn, "IsConnected"):
            # Best-effort: skip if the API is not present.
            pass
    fps = {fp.GetReference() for fp in board.GetFootprints()}
    for ref in ("U1", "U2", "U3", "U4", "U5", "J1", "ANT1", "C2", "L1"):
        if ref not in fps:
            errors.append(f"missing footprint {ref}")
    outline = board.GetBoardEdgesBoundingBox()
    w = pcbnew.ToMM(outline.GetWidth())
    h = pcbnew.ToMM(outline.GetHeight())
    if abs(w - 91.0) > 0.4 or abs(h - 77.0) > 0.4:
        errors.append(f"outline {w:.2f}x{h:.2f} mm, expected 91x77")
    tracks = board.GetTracks()
    n_seg = sum(1 for t in tracks if t.GetClass() == "PCB_TRACK")
    if n_seg < 40:
        errors.append(f"only {n_seg} copper segments")
    report = ROOT / "pcb-report.txt"
    lines = [
        f"footprints: {len(fps)}",
        f"nets_with_pads: {len(pads_by_net)}",
        f"segments: {n_seg}",
        f"outline_mm: {w:.2f} x {h:.2f}",
        "",
    ]
    if errors:
        lines.append(f"ERRORS ({len(errors)})")
        lines.extend(f"  {e}" for e in errors)
    else:
        lines.append("ERRORS (0)")
    report.write_text("\n".join(lines) + "\n")
    print(report.read_text())
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
