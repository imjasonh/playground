#!/usr/bin/env python3
"""Shared placement, footprint, and fabrication helpers for the EVT board."""

from __future__ import annotations

import re
import subprocess
from pathlib import Path

import pcbnew

HERE = Path(__file__).resolve().parent
BOARD = HERE / "inkbot-magsafe.kicad_pcb"
NETLIST = Path("/tmp/inkbot.net")
FP_ROOT = Path("/usr/share/kicad/footprints")
LOCAL_FP_ROOT = HERE / "inkbot_magsafe.pretty"
FAB = HERE / "fab"

BOARD_W, BOARD_H = 60.0, 99.0
BAT_W, BAT_H, BAT_CY = 34.0, 23.0, 70.0
RING_CX, RING_CY, RING_RADIUS = 30.0, 30.0, 27.0
CX = BOARD_W / 2

# Parts mount on the back. The magnetic and coil keep-out occupies the top,
# the protected cell occupies x=13..47 and y=58.5..81.5, and the module,
# panel circuitry, connectors, and test pads fit around those two regions.
PLACEMENT = {
    # The rotated module sits flush with the left edge, antenna first. Its
    # antenna occupies x=0..4.6 mm and must have no copper on any layer.
    "U1": (8.3, 89.0, 90),
    "U3": (52.0, 60.0, 0),
    "U4": (37.0, 87.0, 0),
    "U5": (23.5, 91.0, 0),
    "J1": (45.0, 94.0, 0),
    "J2": (53.0, 77.0, 0),
    "J3": (7.0, 52.5, 0),
    "L1": (41.5, 87.0, 0),
    "Q1": (45.5, 87.0, 0),
    "Q2": (53.0, 70.0, 0),
    "D1": (57.0, 90.0, 0),
    "D2": (55.0, 87.0, 0),
    "D3": (50.0, 87.0, 0),
    "Y1": (20.5, 86.2, 90),
    # Qi resonance, clamp, communication, and output network.
    "C1": (3.0, 57.0, 0),
    "C2": (7.0, 57.0, 0),
    "C3": (11.0, 57.0, 0),
    "C4": (3.0, 60.0, 0),
    "C5": (7.0, 60.0, 0),
    "C6": (3.0, 69.0, 0),
    "C7": (11.0, 69.0, 0),
    "C8": (2.3, 66.0, 0),
    "C9": (11.0, 66.0, 0),
    "C10": (2.5, 62.5, 0),
    "C11": (11.0, 63.0, 0),
    "C12": (2.55, 72.0, 0),
    "C13": (6.4, 74.5, 0),
    "C14": (10.7, 72.0, 0),
    "C15": (2.55, 78.5, 0),
    "C16": (6.4, 77.0, 0),
    "R1": (10.5, 59.5, 0),
    "R2": (10.5, 61.5, 0),
    "R3": (10.25, 75.0, 0),
    "R4": (10.25, 78.0, 0),
    "U2": (7.0, 65.5, 0),
    # Charger, protected-cell connector, and battery ADC network.
    "C17": (49.0, 64.0, 0),
    "C18": (52.5, 64.0, 0),
    "C19": (56.0, 64.0, 0),
    "C20": (24.5, 82.8, 0),
    "R5": (49.0, 67.0, 0),
    "R6": (52.0, 67.0, 0),
    "R7": (56.0, 67.0, 0),
    "R8": (49.0, 70.0, 0),
    "R9": (18.5, 82.8, 0),
    "R10": (21.5, 82.8, 0),
    # Module supply and LFXO.
    "C21": (18.5, 90.0, 0),
    "C22": (18.5, 94.0, 0),
    "C23": (23.5, 85.0, 0),
    "C24": (23.5, 87.5, 0),
    "C38": (25.0, 96.0, 90),
    # Panel LDO and SSD1677 boost network.
    "C26": (28.0, 87.0, 0),
    "C27": (32.5, 87.0, 0),
    "C28": (29.0, 83.2, 0),
    "C29": (33.0, 83.2, 0),
    "C30": (37.0, 83.2, 0),
    "C31": (41.0, 83.2, 0),
    "C32": (45.0, 83.2, 0),
    "C33": (49.0, 83.2, 0),
    "C34": (53.0, 83.2, 0),
    "C35": (57.0, 83.2, 0),
    "C36": (29.0, 90.0, 0),
    "C37": (33.0, 90.0, 0),
    "R11": (29.0, 93.0, 0),
    "R12": (33.0, 93.0, 0),
    # SWD and rail test pads.
    "TP1": (29.0, 96.0, 0),
    "TP2": (32.0, 96.0, 0),
    "TP3": (29.0, 98.0, 0),
    "TP4": (32.0, 98.0, 0),
    "TP5": (57.5, 97.0, 0),
    "TP6": (58.0, 58.0, 0),
    "TP7": (58.0, 62.0, 0),
    "TP8": (58.0, 74.0, 0),
    "TP9": (58.0, 78.0, 0),
}

GND = "GND"
SYS = "/SYS"
CLEAR = 0.15


def to_nm(value_mm: float) -> int:
    return int(round(value_mm * 1e6))


mm = to_nm
TRACK_W = mm(0.2)
VIA_D = mm(0.6)
VIA_DRILL = mm(0.3)


def parse_netlist(path: Path):
    """Return component footprints and net nodes from a KiCad netlist."""
    text = path.read_text()
    components = {}
    for match in re.finditer(
        r'\(comp \(ref "([^"]+)"\)(.*?)(?=\(comp \(ref |\(libparts)',
        text,
        re.S,
    ):
        reference, body = match.group(1), match.group(2)
        footprint = re.search(r'\(footprint "([^"]+)"\)', body)
        components[reference] = footprint.group(1) if footprint else ""

    nets = {}
    for match in re.finditer(
        r'\(net \(code "\d+"\) \(name "([^"]+)"\)(.*?)(?=\(net \(code|\)\s*\Z|\n\s*\)\s*\Z)',
        text,
        re.S,
    ):
        name, body = match.group(1), match.group(2)
        nodes = re.findall(r'\(node \(ref "([^"]+)"\) \(pin "([^"]+)"\)', body)
        if nodes:
            nets[name] = nodes
    return components, nets


def load_fp(library_name: str):
    """Load a system or project footprint and retain its library identifier."""
    library, name = library_name.split(":", 1)
    root = LOCAL_FP_ROOT if library == "inkbot_magsafe" else FP_ROOT / f"{library}.pretty"
    footprint = pcbnew.FootprintLoad(str(root), name)
    if footprint is None:
        raise SystemExit(f"missing footprint {library_name}")
    footprint.SetFPID(pcbnew.LIB_ID(library, name))
    return footprint


def export_fab() -> None:
    """Export Gerbers, drill data, and the pick-and-place file."""
    FAB.mkdir(exist_ok=True)

    def run(arguments):
        result = subprocess.run(arguments, capture_output=True, text=True)
        if result.returncode:
            raise SystemExit(result.stderr.strip())

    run(["kicad-cli", "pcb", "export", "gerbers", "-o", f"{FAB}/", str(BOARD)])
    run(["kicad-cli", "pcb", "export", "drill", "-o", f"{FAB}/", str(BOARD)])
    run(
        [
            "kicad-cli",
            "pcb",
            "export",
            "pos",
            "-o",
            str(FAB / "inkbot-magsafe-pos.csv"),
            "--format",
            "csv",
            "--units",
            "mm",
            str(BOARD),
        ]
    )
    run(
        [
            "kicad-cli",
            "pcb",
            "export",
            "pdf",
            "-o",
            str(FAB / "inkbot-magsafe-bottom-assembly.pdf"),
            "--layers",
            "B.Fab,B.CrtYd,Edge.Cuts",
            "--mirror",
            "--black-and-white",
            str(BOARD),
        ]
    )
    run(
        [
            "kicad-cli",
            "pcb",
            "export",
            "step",
            "--force",
            "--board-only",
            "-o",
            str(FAB / "inkbot-magsafe-board.step"),
            str(BOARD),
        ]
    )
    run(
        [
            "kicad-cli",
            "sch",
            "export",
            "pdf",
            "-o",
            str(FAB / "inkbot-magsafe-schematic.pdf"),
            str(HERE / "inkbot-magsafe.kicad_sch"),
        ]
    )


def main() -> None:
    raise SystemExit("run route_freerouting.py to place, route, and export the board")


if __name__ == "__main__":
    main()
