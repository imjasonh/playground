#!/usr/bin/env python3
"""DRC substitute for KiCad 7 (no `kicad-cli pcb drc`).

KiCad 8+ can run:
  kicad-cli pcb drc --format report --output fab/drc-report.txt inkbot-magsafe.kicad_pcb

This environment has KiCad 7.0, whose CLI only exports Gerbers. This script
loads the board via pcbnew and checks:

  - unrouted multi-pad signal nets (no tracks/vias/zones)
  - track width vs design-rule minimum
  - same-layer centerline crossings between different nets
  - parallel clearance (skipping endpoint-adjacent via/pad joins)
  - empty copper zones

Usage:
  python3 run_drc.py

Writes fab/drc-report.txt and exits 1 if any ERRORS.
"""

from __future__ import annotations

import math
import sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, "/usr/lib/python3/dist-packages")
import pcbnew  # noqa: E402

HERE = Path(__file__).resolve().parent
BOARD_PATH = HERE / "inkbot-magsafe.kicad_pcb"
OUT = HERE / "fab" / "drc-report.txt"
ZONE_NETS = {"GND", "/VSYS", "/BAT", "VSYS", "BAT"}


def dist(ax: float, ay: float, bx: float, by: float) -> float:
    return math.hypot(ax - bx, ay - by)


def seg_min_dist(a, b) -> float:
    ax1, ay1 = a.GetStart().x, a.GetStart().y
    ax2, ay2 = a.GetEnd().x, a.GetEnd().y
    bx1, by1 = b.GetStart().x, b.GetStart().y
    bx2, by2 = b.GetEnd().x, b.GetEnd().y

    def dps(px, py, x1, y1, x2, y2):
        dx, dy = x2 - x1, y2 - y1
        if dx == 0 and dy == 0:
            return math.hypot(px - x1, py - y1)
        t = max(0, min(1, ((px - x1) * dx + (py - y1) * dy) / (dx * dx + dy * dy)))
        return math.hypot(px - (x1 + t * dx), py - (y1 + t * dy))

    return min(
        dps(ax1, ay1, bx1, by1, bx2, by2),
        dps(ax2, ay2, bx1, by1, bx2, by2),
        dps(bx1, by1, ax1, ay1, ax2, ay2),
        dps(bx2, by2, ax1, ay1, ax2, ay2),
    )


def endpoints_near(a, b, thresh: float) -> bool:
    pts_a = [(a.GetStart().x, a.GetStart().y), (a.GetEnd().x, a.GetEnd().y)]
    pts_b = [(b.GetStart().x, b.GetStart().y), (b.GetEnd().x, b.GetEnd().y)]
    return any(dist(pa[0], pa[1], pb[0], pb[1]) < thresh for pa in pts_a for pb in pts_b)


def segments_cross(a, b) -> bool:
    def orient(px, py, qx, qy, rx, ry):
        v = (qy - py) * (rx - qx) - (qx - px) * (ry - qy)
        if abs(v) < 1:
            return 0
        return 1 if v > 0 else 2

    p1x, p1y = a.GetStart().x, a.GetStart().y
    q1x, q1y = a.GetEnd().x, a.GetEnd().y
    p2x, p2y = b.GetStart().x, b.GetStart().y
    q2x, q2y = b.GetEnd().x, b.GetEnd().y
    o1 = orient(p1x, p1y, q1x, q1y, p2x, p2y)
    o2 = orient(p1x, p1y, q1x, q1y, q2x, q2y)
    o3 = orient(p2x, p2y, q2x, q2y, p1x, p1y)
    o4 = orient(p2x, p2y, q2x, q2y, q1x, q1y)
    if o1 != o2 and o3 != o4:
        if endpoints_near(a, b, int(0.05 * 1e6)):
            return False
        return True
    return False


def main() -> int:
    if not BOARD_PATH.exists():
        print(f"missing board: {BOARD_PATH}", file=sys.stderr)
        return 2

    OUT.parent.mkdir(parents=True, exist_ok=True)
    board = pcbnew.LoadBoard(str(BOARD_PATH))
    settings = board.GetDesignSettings()
    min_clear = settings.m_MinClearance
    min_track = settings.m_TrackMinWidth

    errors: list[str] = []
    warnings: list[str] = []

    conn = board.GetConnectivity()
    conn.RecalculateRatsnest()

    net_pads: dict[str, list[str]] = defaultdict(list)
    for fp in board.GetFootprints():
        for pad in fp.Pads():
            if pad.GetAttribute() == pcbnew.PAD_ATTRIB_NPTH:
                continue
            net = pad.GetNetname()
            if not net:
                ref = fp.GetReference()
                # Unused module / FPC / LDO NC pins are expected.
                if ref in ("U1", "J1") or (ref == "U5" and pad.GetNumber() in ("", "21")):
                    continue
                if ref == "U4" and pad.GetNumber() == "4":
                    continue
                warnings.append(f"NO_NET: {ref}.{pad.GetNumber()}")
                continue
            net_pads[net].append(f"{fp.GetReference()}.{pad.GetNumber()}")

    for name, pads in sorted(net_pads.items()):
        if name in ZONE_NETS or name == "GND":
            continue
        tracks = [
            t
            for t in board.GetTracks()
            if t.GetNetname() == name and t.Type() != pcbnew.PCB_VIA_T
        ]
        vias = [
            t
            for t in board.GetTracks()
            if t.GetNetname() == name and t.Type() == pcbnew.PCB_VIA_T
        ]
        zones = [
            z for z in board.Zones() if z.GetNetname() == name and z.GetFilledArea() > 0
        ]
        if len(pads) >= 2 and not tracks and not vias and not zones:
            errors.append(
                f"UNROUTED: {name} — {len(pads)} pads, no tracks/vias/zones: {pads}"
            )

    for t in board.GetTracks():
        if t.Type() == pcbnew.PCB_VIA_T:
            continue
        if t.GetWidth() < min_track:
            errors.append(
                f"TRACK_WIDTH: {t.GetNetname()} "
                f"{t.GetWidth() / 1e6:.3f}mm < {min_track / 1e6:.3f}mm"
            )

    tracks = [t for t in board.GetTracks() if t.Type() != pcbnew.PCB_VIA_T]
    crossings: list[tuple[str, str, int]] = []
    parallel_close: list[tuple[float, str, str, int]] = []
    for i, a in enumerate(tracks):
        for b in tracks[i + 1 :]:
            if a.GetNetCode() == b.GetNetCode() or a.GetLayer() != b.GetLayer():
                continue
            if segments_cross(a, b):
                crossings.append((a.GetNetname(), b.GetNetname(), a.GetLayer()))
                continue
            if endpoints_near(a, b, int(0.35 * 1e6)):
                continue
            gap = seg_min_dist(a, b) - (a.GetWidth() + b.GetWidth()) / 2
            if gap < min_clear:
                alen = dist(a.GetStart().x, a.GetStart().y, a.GetEnd().x, a.GetEnd().y)
                blen = dist(b.GetStart().x, b.GetStart().y, b.GetEnd().x, b.GetEnd().y)
                if alen < int(0.2 * 1e6) or blen < int(0.2 * 1e6):
                    continue
                parallel_close.append((gap, a.GetNetname(), b.GetNetname(), a.GetLayer()))

    seen: set[tuple] = set()
    for na, nb, layer in crossings:
        key = tuple(sorted([na, nb]) + [layer])
        if key in seen:
            continue
        seen.add(key)
        errors.append(f"CROSSING: {na} vs {nb} layer={layer}")

    seen2: set[tuple] = set()
    for gap, na, nb, layer in sorted(parallel_close, key=lambda x: x[0])[:40]:
        key = tuple(sorted([na, nb]) + [layer])
        if key in seen or key in seen2:
            continue
        seen2.add(key)
        kind = "SHORT" if gap < 0 else "CLEARANCE"
        errors.append(f"{kind}: {na} vs {nb} layer={layer} gap={gap / 1e6:.3f}mm")

    for z in board.Zones():
        if z.GetNetname() and z.GetFilledArea() == 0:
            warnings.append(f"ZONE_EMPTY: {z.GetNetname()} layer={z.GetLayerName()}")

    n_tracks = len(tracks)
    n_vias = sum(1 for t in board.GetTracks() if t.Type() == pcbnew.PCB_VIA_T)
    errors = list(dict.fromkeys(errors))
    warnings = list(dict.fromkeys(warnings))

    lines = [
        "=" * 72,
        "inkbot-magsafe DRC report",
        "Engine: Python/pcbnew substitute (KiCad 7.0 — no `kicad-cli pcb drc`)",
        f"Board: {BOARD_PATH}",
        f"Rules: min clearance {min_clear / 1e6:.3f} mm, min track {min_track / 1e6:.3f} mm",
        f"Stats: {len(list(board.GetFootprints()))} footprints, "
        f"{n_tracks} track segs, {n_vias} vias",
        "=" * 72,
        "",
        f"ERRORS ({len(errors)})",
        "-" * 40,
        *(errors or ["(none)"]),
        "",
        f"WARNINGS ({len(warnings)})",
        "-" * 40,
        *(warnings or ["(none)"]),
        "",
        "Notes:",
        "  - Endpoint-adjacent pairs (via/pad joins) excluded from clearance noise",
        "  - CROSSING = centerlines intersect on same layer (different nets)",
        "  - Full silk/courtyard/hole DRC still needs pcbnew GUI or KiCad 8+ CLI",
        "  - Re-run GUI DRC before ordering PCBs",
        "",
    ]
    OUT.write_text("\n".join(lines))
    print(OUT.read_text())
    print(f"Wrote {OUT}", file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
