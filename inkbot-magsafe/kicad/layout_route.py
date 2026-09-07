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
BAT_W, BAT_H, BAT_CY = 33.0, 22.0, 70.0
RING_CX, RING_CY, RING_RADIUS = 30.0, 30.0, 27.0
CX = BOARD_W / 2

# Parts mount on the back. The magnetic and coil keep-out occupies the top,
# the protected cell occupies x=13.5..46.5 and y=59..81, and the module,
# panel circuitry, connectors, and test pads fit around those two regions.
PLACEMENT = {
    "U1": (19.0, 89.0, 90),
    "U2": (7.0, 59.0, 0),
    "U3": (52.0, 60.0, 0),
    "U4": (37.0, 87.0, 0),
    "J1": (45.0, 94.0, 0),
    "J2": (53.0, 77.0, 0),
    "J3": (7.0, 54.0, 0),
    "L1": (41.5, 87.0, 0),
    "Q1": (45.5, 87.0, 0),
    "D1": (57.0, 90.0, 0),
    "D2": (55.0, 87.0, 0),
    "D3": (50.0, 87.0, 0),
    "Y1": (5.5, 96.5, 90),
    "RT2": (11.0, 82.0, 0),
    # Qi resonance, clamp, communication, and output network.
    "C1": (3.0, 64.0, 0),
    "C2": (7.0, 64.0, 0),
    "C3": (11.0, 64.0, 0),
    "C4": (3.0, 67.0, 0),
    "C5": (7.0, 67.0, 0),
    "C6": (11.0, 67.0, 0),
    "C7": (3.0, 70.0, 0),
    "C8": (7.0, 70.0, 0),
    "C9": (11.0, 70.0, 0),
    "C10": (3.0, 73.0, 0),
    "C11": (7.0, 73.0, 0),
    "C12": (11.0, 73.0, 0),
    "C13": (3.0, 76.0, 0),
    "C14": (7.0, 76.0, 0),
    "C15": (11.0, 76.0, 0),
    "C16": (3.0, 79.0, 0),
    "R1": (7.0, 79.0, 0),
    "R2": (11.0, 79.0, 0),
    "R3": (3.0, 82.0, 0),
    "R4": (7.0, 82.0, 0),
    # Charger, protected-cell connector, and battery ADC network.
    "C17": (49.0, 64.0, 0),
    "C18": (52.0, 64.0, 0),
    "C19": (56.0, 64.0, 0),
    "C20": (52.0, 70.0, 0),
    "R5": (49.0, 67.0, 0),
    "R6": (52.0, 67.0, 0),
    "R7": (56.0, 67.0, 0),
    "R8": (49.0, 70.0, 0),
    "R9": (56.0, 70.0, 0),
    "R10": (49.0, 73.0, 0),
    "C25": (52.0, 73.0, 0),
    # Module supply and LFXO.
    "C21": (10.0, 97.0, 0),
    "C22": (14.0, 97.0, 0),
    "C23": (18.0, 97.0, 0),
    "C24": (22.0, 97.0, 0),
    # Panel LDO and SSD1677 boost network.
    "C26": (29.0, 87.0, 0),
    "C27": (33.0, 87.0, 0),
    "C28": (29.0, 82.5, 0),
    "C29": (33.0, 82.5, 0),
    "C30": (37.0, 82.5, 0),
    "C31": (41.0, 82.5, 0),
    "C32": (45.0, 82.5, 0),
    "C33": (49.0, 82.5, 0),
    "C34": (53.0, 82.5, 0),
    "C35": (57.0, 82.5, 0),
    "C36": (29.0, 90.0, 0),
    "C37": (33.0, 90.0, 0),
    "R11": (29.0, 93.0, 0),
    "R12": (33.0, 93.0, 0),
    "R13": (56.0, 93.0, 0),
    "R14": (59.0, 93.0, 90),
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
VIA_D = mm(0.5)
VIA_DRILL = mm(0.3)

POWER_WIDTHS = {
    "/BAT": mm(0.4),
    "/PANEL_3V0": mm(0.3),
    "/PANEL_PUMP": mm(0.3),
    "/PANEL_SW": mm(0.3),
    "/PANEL_VGH": mm(0.3),
    "/PANEL_VGL": mm(0.3),
    "/QI_AC1": mm(0.3),
    "/QI_AC2": mm(0.3),
    "/QI_COIL_A": mm(0.3),
    "/QI_OUT": mm(0.4),
    "/QI_RECT": mm(0.3),
    "/SYS": mm(0.4),
    "GND": mm(0.3),
}


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


def main() -> None:
    raise SystemExit("run route_freerouting.py to place, route, and export the board")


if __name__ == "__main__":
    main()
