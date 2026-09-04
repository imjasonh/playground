#!/usr/bin/env python3
"""Validate the nfc-eink schematic against a KiCad 7 netlist.

KiCad 7's CLI has no `sch erc`. Export a kicadsexpr netlist and reject
unexpected unconnected IC pins plus missing power or bus nets.
"""

from __future__ import annotations

import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCH = ROOT / "nfc-eink.kicad_sch"

# MCU GPIO and EPD test pins that the design leaves open.
ALLOW_UNCONNECTED = {
    ("U5", n)
    for n in (
        "1",
        "2",
        "3",
        "8",
        "9",
        "12",
        "20",
        "21",
        "22",
        "23",
        "24",
        "25",
        "26",
        "27",
        "29",
        "30",
        "31",
        "32",
        "33",
        "34",
        "38",
        "39",
        "40",
        "41",
        "42",
        "43",
        "47",
        "48",
    )
} | {("J1", n) for n in ("1", "4", "6", "7", "19")}

REQUIRED_NETS = {
    "+3V3": [("U5", "6"), ("U1", "6"), ("U2", "6")],
    "GND": [("U5", "7"), ("U1", "2"), ("U2", "4")],
    "VOUT_EH": [("U1", "7"), ("D1", "2")],  # D1 pin 2 = anode
    "VHARV_OR": [("D1", "1"), ("R1", "1")],  # D1 pin 1 = cathode
    "VSTORE": [("U2", "3"), ("C2", "1")],
    "+3V3_EPD": [("U3", "6"), ("J1", "16")],
    "NFC_LA": [("U1", "1"), ("ANT1", "1")],
    "NFC_LB": [("U1", "8"), ("ANT1", "2")],
    "I2C_SCL": [("U1", "3"), ("U5", "45")],
    "I2C_SDA": [("U1", "5"), ("U5", "46")],
    "NFC_FD": [("U1", "4"), ("U5", "44")],
    "NRST": [("U4", "2"), ("U5", "10")],
    "EPD_MOSI": [("U5", "18"), ("J1", "14")],
    "EPD_SCK": [("U5", "16"), ("J1", "13")],
    "EPD_CS": [("U5", "15"), ("J1", "12")],
    "EPD_DC": [("U5", "28"), ("J1", "11")],
    "EPD_RST": [("U5", "37"), ("J1", "10")],
    "EPD_BUSY": [("U5", "17"), ("J1", "9")],
    "EPD_PWR_EN": [("U5", "19"), ("U3", "3")],
    "BOOST_FB": [("U2", "1"), ("R2", "2")],
}

MUST_HAVE_REFS = ["U1", "U2", "U3", "U4", "U5", "D1", "L1", "Q1", "J1", "ANT1", "C2"]


def extract_balanced(text: str, start: int) -> str:
    depth = 0
    for i in range(start, len(text)):
        if text[i] == "(":
            depth += 1
        elif text[i] == ")":
            depth -= 1
            if depth == 0:
                return text[start : i + 1]
    raise ValueError("unbalanced")


def parse_netlist(text: str) -> tuple[set[str], dict[str, list[tuple[str, str]]]]:
    refs: set[str] = set()
    for m in re.finditer(r'\(comp \(ref "([^"]+)"\)', text):
        refs.add(m.group(1))
    nets: dict[str, list[tuple[str, str]]] = {}
    idx = text.find("(nets")
    if idx < 0:
        raise ValueError("netlist has no (nets")
    blob = extract_balanced(text, idx)
    pos = 0
    while True:
        i = blob.find("(net ", pos)
        if i < 0:
            break
        block = extract_balanced(blob, i)
        pos = i + 4
        nm = re.search(r'\(name "([^"]+)"\)', block)
        if not nm:
            continue
        nodes = re.findall(r'\(node \(ref "([^"]+)"\) \(pin "([^"]+)"\)', block)
        nets[nm.group(1)] = [(a, b) for a, b in nodes]
    return refs, nets


def run() -> int:
    net_path = ROOT / "nfc-eink.net"
    try:
        subprocess.run(
            [
                "kicad-cli",
                "sch",
                "export",
                "netlist",
                "--format",
                "kicadsexpr",
                "--output",
                str(net_path),
                str(SCH),
            ],
            check=True,
            capture_output=True,
            text=True,
        )
    except subprocess.CalledProcessError as exc:
        print(exc.stderr or exc.stdout, file=sys.stderr)
        return 2
    refs, nets = parse_netlist(net_path.read_text())
    errors: list[str] = []

    for ref in MUST_HAVE_REFS:
        if ref not in refs:
            errors.append(f"missing component {ref}")

    node_to_net: dict[tuple[str, str], str] = {}
    for name, nodes in nets.items():
        for node in nodes:
            node_to_net[node] = name

    for name, nodes in nets.items():
        if not name.startswith("unconnected-"):
            continue
        for ref, pin in nodes:
            if (ref, pin) in ALLOW_UNCONNECTED:
                continue
            if ref.startswith("#"):
                continue
            errors.append(f"{ref} pin {pin} is unconnected ({name})")

    for net, members in REQUIRED_NETS.items():
        have = set(nets.get(net, []))
        if not have:
            errors.append(f"missing net {net}")
            continue
        for ref, pin in members:
            if (ref, pin) not in have:
                got = node_to_net.get((ref, pin), "absent")
                errors.append(f"{ref} pin {pin} should be on {net}, is on {got}")

    report = ROOT / "erc-report.txt"
    lines = [
        f"components: {len(refs)}",
        f"nets: {len(nets)}",
        "",
    ]
    if errors:
        lines.append(f"ERRORS ({len(errors)})")
        lines.extend(f"  {e}" for e in sorted(errors))
    else:
        lines.append("ERRORS (0)")
    report.write_text("\n".join(lines) + "\n")
    print(report.read_text())
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(run())
