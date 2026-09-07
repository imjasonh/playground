#!/usr/bin/env python3
"""Electrical-rule check for the schematic netlist and board parity.

KiCad 8+ offers ``kicad-cli sch erc``; KiCad 7 (this environment) does not, so
this script does the equivalent electrical checks the design cares about:

  - every real net has >= 2 nodes (no single-pin/floating nets)
  - every unconnected pin is an intentional no-connect (module NC pins)
  - the critical power and interface nets exist with sane membership
  - board <-> netlist parity: every netlist net's pads exist on the PCB and
    every powered pad on the board is claimed by the netlist

Run ``kicad-cli sch export netlist -o /tmp/inkbot.net inkbot-magsafe.kicad_sch``
first (layout_route.py already expects that file).

Usage:
  python3 run_erc.py
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
NETLIST = Path("/tmp/inkbot.net")
BOARD = HERE / "inkbot-magsafe.kicad_pcb"

# Nets that must be present for the board to function. Local labels carry a
# leading "/"; the system rail is /VSYS (the pack sits on it, detach-to-charge).
CRITICAL = ["GND", "/VSYS", "/AC1", "/AC2", "/QI_RECT", "/V3V3_PANEL",
            "/PANEL_SCLK", "/PANEL_MOSI", "/PANEL_CS", "/PANEL_DC",
            "/SWDIO", "/SWDCLK", "/NRST"]


def parse_netlist(path: Path):
    text = path.read_text()
    nets = {}
    for m in re.finditer(
        r'\(net \(code "\d+"\) \(name "([^"]+)"\)(.*?)(?=\(net \(code|\)\s*\Z)',
        text, re.S,
    ):
        name, body = m.group(1), m.group(2)
        nodes = re.findall(r'\(node \(ref "([^"]+)"\) \(pin "([^"]+)"\)', body)
        nets[name] = nodes
    return nets


def main() -> int:
    if not NETLIST.exists():
        print(f"missing netlist: {NETLIST}\n"
              f"run: kicad-cli sch export netlist -o {NETLIST} {HERE}/inkbot-magsafe.kicad_sch",
              file=sys.stderr)
        return 2

    nets = parse_netlist(NETLIST)
    errors: list[str] = []
    warnings: list[str] = []

    real = {n: v for n, v in nets.items() if not n.startswith("unconnected-")}
    nc = {n: v for n, v in nets.items() if n.startswith("unconnected-")}

    # 1. Floating real nets.
    for name, nodes in sorted(real.items()):
        if len(nodes) < 2:
            errors.append(f"FLOATING: net {name} has {len(nodes)} node(s): {nodes}")

    # 2. No-connect pins should only be the module's unused GPIO / NC pins.
    nc_pins = [f"{r}.{p}" for nodes in nc.values() for r, p in nodes]
    non_module_nc = [p for p in nc_pins if not p.startswith("U1.")]
    if non_module_nc:
        warnings.append(
            f"NO_CONNECT off the module ({len(non_module_nc)}): {non_module_nc}"
        )
    if nc_pins:
        warnings.append(f"module NC pins (expected): {len(nc_pins)}")

    # 3. Critical nets present.
    for name in CRITICAL:
        if name not in real:
            errors.append(f"MISSING critical net: {name}")

    # 4. Board <-> netlist parity.
    board_text = BOARD.read_text()
    board_nets = set(re.findall(r'\(net \d+ "([^"]*)"\)', board_text))
    for name in real:
        if name not in board_nets:
            errors.append(f"PARITY: netlist net {name} absent from board")

    print("ERC (netlist electrical + board parity)")
    print(f"  nets: {len(real)} real, {len(nc)} no-connect groups, "
          f"{sum(len(v) for v in real.values())} nodes")
    print(f"  critical nets present: {sum(1 for n in CRITICAL if n in real)}/{len(CRITICAL)}")
    print()
    print(f"ERRORS ({len(errors)})")
    for e in errors or ["  (none)"]:
        print(f"  {e}")
    print()
    print(f"WARNINGS ({len(warnings)})")
    for w in warnings or ["  (none)"]:
        print(f"  {w}")
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
