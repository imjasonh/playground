#!/usr/bin/env python3
"""Check electrical pin contracts, BOM coverage, and board parity.

KiCad 8 or later provides ``kicad-cli sch erc``. KiCad 7 does not, so this
script enforces the design-specific contracts that generic ERC cannot prove:

  - every IC and connector pin is on the intended net
  - every no-connect is explicitly allowed
  - every real net has at least two nodes
  - the procurement BOM covers every schematic reference
  - every placed pad has the same net as the schematic

Export the netlist before running this script. ``route_freerouting.py`` does
that automatically.
"""

from __future__ import annotations

import csv
import re
import sys
from pathlib import Path

sys.path.insert(0, "/usr/lib/python3/dist-packages")
import pcbnew  # noqa: E402

HERE = Path(__file__).resolve().parent
NETLIST = Path("/tmp/inkbot.net")
BOARD = HERE / "inkbot-magsafe.kicad_pcb"
BOM = HERE.parents[1] / "docs" / "inkbot-magsafe-bom.csv"

PIN_NETS = {
    # Raytac MDBT50Q-1MV2.
    ("U1", "1"): "GND",
    ("U1", "2"): "GND",
    ("U1", "8"): "/QI_PRESENT",
    ("U1", "9"): "/QI_EN1",
    ("U1", "10"): "/SYS_SENSE",
    ("U1", "11"): "/PANEL_TEMP_SENSE",
    ("U1", "12"): "/PANEL_PWR_EN",
    ("U1", "14"): "/PANEL_BUSY",
    ("U1", "15"): "GND",
    ("U1", "16"): "/PANEL_TEMP_EXCITE",
    ("U1", "17"): "/XL1",
    ("U1", "18"): "/XL2",
    ("U1", "20"): "/CHG_INT_N",
    ("U1", "21"): "/CHG_PG_N",
    ("U1", "22"): "/CHG_ENABLE",
    ("U1", "23"): "/CHG_SDA",
    ("U1", "24"): "/CHG_SCL",
    ("U1", "25"): "/QI_EN2",
    ("U1", "26"): "/PANEL_RST",
    ("U1", "27"): "/PANEL_SCLK",
    ("U1", "28"): "/MCU_3V0",
    ("U1", "30"): "/MCU_3V0",
    ("U1", "32"): "GND",
    ("U1", "33"): "GND",
    ("U1", "39"): "/PANEL_MOSI",
    ("U1", "40"): "/NRST",
    ("U1", "41"): "/PANEL_CS",
    ("U1", "44"): "/PANEL_DC",
    ("U1", "51"): "/SWDIO",
    ("U1", "53"): "/SWDCLK",
    ("U1", "55"): "GND",
    # BQ51013C.
    ("U2", "1"): "GND",
    ("U2", "2"): "/QI_AC1",
    ("U2", "3"): "/QI_BOOT1",
    ("U2", "4"): "/QI_OUT",
    ("U2", "5"): "/QI_CLAMP1",
    ("U2", "6"): "/QI_COMM1",
    ("U2", "7"): "/QI_PRESENT",
    ("U2", "9"): "GND",
    ("U2", "10"): "/QI_EN1",
    ("U2", "11"): "/QI_EN2",
    ("U2", "12"): "/QI_ILIM",
    ("U2", "13"): "/QI_COIL_NTC",
    ("U2", "14"): "/QI_FOD",
    ("U2", "15"): "/QI_COMM2",
    ("U2", "16"): "/QI_CLAMP2",
    ("U2", "17"): "/QI_BOOT2",
    ("U2", "18"): "/QI_RECT",
    ("U2", "19"): "/QI_AC2",
    ("U2", "20"): "GND",
    ("U2", "21"): "GND",
    # BQ25186.
    ("U3", "1"): "/SYS",
    ("U3", "2"): "/BAT",
    ("U3", "3"): "/CHG_PG_N",
    ("U3", "4"): "/CHG_CE_N",
    ("U3", "5"): "GND",
    ("U3", "6"): "/BAT_NTC",
    ("U3", "7"): "/CHG_SDA",
    ("U3", "8"): "/CHG_SCL",
    ("U3", "9"): "/CHG_INT_N",
    ("U3", "10"): "/QI_OUT",
    ("U3", "11"): "GND",
    # TPS7A2030P.
    ("U4", "1"): "/SYS",
    ("U4", "2"): "GND",
    ("U4", "3"): "/PANEL_PWR_EN",
    ("U4", "5"): "/PANEL_3V0",
    # TPS7A0230P MCU regulator.
    ("U5", "1"): "/SYS",
    ("U5", "2"): "GND",
    ("U5", "3"): "/SYS",
    ("U5", "5"): "/MCU_3V0",
    # Panel connector.
    ("J1", "2"): "/PANEL_GDR",
    ("J1", "3"): "/PANEL_RESE",
    ("J1", "5"): "/PANEL_VSH2",
    ("J1", "8"): "GND",
    ("J1", "9"): "/PANEL_BUSY",
    ("J1", "10"): "/PANEL_RST",
    ("J1", "11"): "/PANEL_DC",
    ("J1", "12"): "/PANEL_CS",
    ("J1", "13"): "/PANEL_SCLK",
    ("J1", "14"): "/PANEL_MOSI",
    ("J1", "15"): "/PANEL_3V0",
    ("J1", "16"): "/PANEL_3V0",
    ("J1", "17"): "GND",
    ("J1", "18"): "/PANEL_VDD",
    ("J1", "20"): "/PANEL_VSH1",
    ("J1", "21"): "/PANEL_VGH",
    ("J1", "22"): "/PANEL_VSL",
    ("J1", "23"): "/PANEL_VGL",
    ("J1", "24"): "/PANEL_VCOM",
    # Battery and coil interfaces.
    ("J2", "1"): "/BAT",
    ("J2", "2"): "/BAT_NTC",
    ("J2", "3"): "GND",
    ("J3", "1"): "/QI_COIL_A",
    ("J3", "2"): "/QI_AC2",
    ("J3", "3"): "/QI_COIL_NTC",
    ("J3", "4"): "GND",
    ("BT1", "1"): "/BAT",
    ("BT1", "2"): "GND",
    ("RT1", "1"): "/BAT_NTC",
    ("RT1", "2"): "GND",
    ("RT2", "1"): "/QI_COIL_NTC",
    ("RT2", "2"): "GND",
    ("L2", "1"): "/QI_COIL_A",
    ("L2", "2"): "/QI_AC2",
    # Panel boost and LFXO.
    ("L1", "1"): "/PANEL_3V0",
    ("L1", "2"): "/PANEL_SW",
    ("Q1", "1"): "/PANEL_GDR",
    ("Q1", "2"): "/PANEL_RESE",
    ("Q1", "3"): "/PANEL_SW",
    ("Q2", "1"): "/CHG_ENABLE",
    ("Q2", "2"): "GND",
    ("Q2", "3"): "/CHG_CE_N",
    ("D1", "1"): "/PANEL_PUMP",
    ("D1", "2"): "/PANEL_VGL",
    ("D2", "1"): "GND",
    ("D2", "2"): "/PANEL_PUMP",
    ("D3", "1"): "/PANEL_VGH",
    ("D3", "2"): "/PANEL_SW",
    ("Y1", "1"): "/XL1",
    ("Y1", "2"): "/XL2",
}

VALUE_CONTRACT = {
    "U1": ("MDBT50Q-1MV2", "RF_Module:Raytac_MDBT50Q"),
    "U2": ("BQ51013C", "Package_DFN_QFN:Texas_VQFN-RHL-20"),
    "U3": ("BQ25186DLHR", "inkbot_magsafe:TI_DLH0010A_WSON-10"),
    "U4": ("TPS7A2030PDBVR", "Package_TO_SOT_SMD:SOT-23-5"),
    "U5": ("TPS7A0230PDBVR", "Package_TO_SOT_SMD:SOT-23-5"),
    "J1": (
        "GDEY0397T81P panel FPC",
        "Connector_FFC-FPC:Hirose_FH12-24S-0.5SH_1x24-1MP_P0.50mm_Horizontal",
    ),
    "J2": (
        "Protected battery + NTC",
        "Connector_Molex:Molex_Pico-EZmate_78171-0003_1x03-1MP_P1.20mm_Vertical",
    ),
    "L1": ("VLS252010CX-100M-1 10uH", "inkbot_magsafe:TDK_VLS252010CX"),
    "Q1": ("Si1308EDL-T1-GE3", "Package_TO_SOT_SMD:SOT-323_SC-70"),
    "Q2": ("2N7002BK,215", "Package_TO_SOT_SMD:SOT-23"),
    "R1": ("845R 1%", "Resistor_SMD:R_0603_1608Metric"),
    "R2": ("200R 1%", "Resistor_SMD:R_0603_1608Metric"),
    "R3": ("20k 1%", "Resistor_SMD:R_0603_1608Metric"),
    "R5": ("100k", "Resistor_SMD:R_0603_1608Metric"),
    "R6": ("1M", "Resistor_SMD:R_0603_1608Metric"),
    "R7": ("10k", "Resistor_SMD:R_0603_1608Metric"),
    "R8": ("10k", "Resistor_SMD:R_0603_1608Metric"),
    "R9": ("1M 1%", "Resistor_SMD:R_0603_1608Metric"),
    "R10": ("330k 1%", "Resistor_SMD:R_0603_1608Metric"),
    "R13": ("10k 1%", "Resistor_SMD:R_0603_1608Metric"),
    "RT3": (
        "NCP18XH103F03RB 10k 3380K",
        "Capacitor_SMD:C_0603_1608Metric",
    ),
    "C1": ("33nF C0G 50V", "Capacitor_SMD:C_0805_2012Metric"),
    "C2": ("33nF C0G 50V", "Capacitor_SMD:C_0805_2012Metric"),
    "C3": ("15nF C0G 50V", "Capacitor_SMD:C_0805_2012Metric"),
    "C16": ("100nF 50V", "Capacitor_SMD:C_0603_1608Metric"),
    "C27": ("100uF 6.3V X5R", "Capacitor_SMD:C_1206_3216Metric"),
    "C30": ("1uF 50V X5R", "Capacitor_SMD:C_0603_1608Metric"),
    "C31": ("4.7uF 35V X7R", "Capacitor_SMD:C_0805_2012Metric"),
    "C32": ("4.7uF 35V X7R", "Capacitor_SMD:C_0805_2012Metric"),
    "C33": ("4.7uF 35V X7R", "Capacitor_SMD:C_0805_2012Metric"),
    "C34": ("4.7uF 35V X7R", "Capacitor_SMD:C_0805_2012Metric"),
    "C35": ("4.7uF 35V X7R", "Capacitor_SMD:C_0805_2012Metric"),
    "C36": ("1uF 50V X5R", "Capacitor_SMD:C_0603_1608Metric"),
    "C37": ("4.7uF 35V X7R", "Capacitor_SMD:C_0805_2012Metric"),
    "C38": ("47uF 10V X5R", "Capacitor_SMD:C_1206_3216Metric"),
}

ALLOWED_EXTRA_BOM_REFS = {"ASSY", "DS1", "MAG1", "MECH1", "PCB1"}
BOARD_ONLY_NETS = {
    ("J1", "MP"): "GND",
    ("J2", "MP"): "GND",
}


def parse_netlist(path: Path):
    text = path.read_text()
    components = {}
    for match in re.finditer(
        r'\(comp \(ref "([^"]+)"\)(.*?)(?=\(comp \(ref |\(libparts)',
        text,
        re.S,
    ):
        reference, body = match.group(1), match.group(2)
        value = re.search(r'\(value "([^"]*)"\)', body)
        footprint = re.search(r'\(footprint "([^"]*)"\)', body)
        components[reference] = {
            "value": value.group(1) if value else "",
            "footprint": footprint.group(1) if footprint else "",
        }

    nets = {}
    for m in re.finditer(
        r'\(net \(code "\d+"\) \(name "([^"]+)"\)(.*?)(?=\(net \(code|\)\s*\Z)',
        text, re.S,
    ):
        name, body = m.group(1), m.group(2)
        nodes = re.findall(r'\(node \(ref "([^"]+)"\) \(pin "([^"]+)"\)', body)
        nets[name] = nodes
    return components, nets


def no_connect_allowed(reference: str, pin: str) -> bool:
    if reference == "U1":
        return (reference, pin) not in PIN_NETS
    return (reference, pin) in {
        ("J1", "1"),
        ("J1", "4"),
        ("J1", "6"),
        ("J1", "7"),
        ("J1", "19"),
        ("U2", "8"),
        ("U4", "4"),
        ("U5", "4"),
    }


def parse_bom(path: Path):
    rows = list(csv.DictReader(path.open(newline="")))
    by_reference = {}
    duplicates = set()
    for row in rows:
        references = row["refs"].split()
        for reference in references:
            if reference in by_reference:
                duplicates.add(reference)
            by_reference[reference] = row
    return rows, by_reference, duplicates


def main() -> int:
    if not NETLIST.exists():
        print(f"missing netlist: {NETLIST}\n"
              f"run: kicad-cli sch export netlist -o {NETLIST} {HERE}/inkbot-magsafe.kicad_sch",
              file=sys.stderr)
        return 2

    if not BOARD.exists() or not BOM.exists():
        print(f"missing board or BOM: {BOARD}, {BOM}", file=sys.stderr)
        return 2

    components, nets = parse_netlist(NETLIST)
    errors: list[str] = []
    warnings: list[str] = []

    real = {n: v for n, v in nets.items() if not n.startswith("unconnected-")}
    nc = {n: v for n, v in nets.items() if n.startswith("unconnected-")}

    for name, nodes in sorted(real.items()):
        if len(nodes) < 2:
            errors.append(f"FLOATING: net {name} has {len(nodes)} node(s): {nodes}")

    node_nets = {
        node: net_name
        for net_name, nodes in real.items()
        for node in nodes
    }
    for node, expected_net in PIN_NETS.items():
        actual_net = node_nets.get(node)
        if actual_net != expected_net:
            errors.append(
                f"PIN_CONTRACT: {node[0]}.{node[1]} expected {expected_net}, "
                f"found {actual_net or 'no connection'}"
            )

    nc_nodes = [node for nodes in nc.values() for node in nodes]
    for reference, pin in nc_nodes:
        if not no_connect_allowed(reference, pin):
            errors.append(f"NO_CONNECT: {reference}.{pin} is not on the allowlist")

    for reference, (expected_value, expected_footprint) in VALUE_CONTRACT.items():
        component = components.get(reference)
        if component is None:
            errors.append(f"COMPONENT: missing {reference}")
            continue
        if component["value"] != expected_value:
            errors.append(
                f"VALUE: {reference} expected {expected_value}, "
                f"found {component['value']}"
            )
        if component["footprint"] != expected_footprint:
            errors.append(
                f"FOOTPRINT: {reference} expected {expected_footprint}, "
                f"found {component['footprint']}"
            )

    rows, bom_by_reference, duplicate_bom_refs = parse_bom(BOM)
    for reference in sorted(duplicate_bom_refs):
        errors.append(f"BOM: duplicate reference {reference}")
    schematic_refs = {
        reference
        for reference in components
        if not reference.startswith(("#FLG", "#PWR"))
    }
    for reference in sorted(schematic_refs - set(bom_by_reference)):
        errors.append(f"BOM: missing schematic reference {reference}")
    for reference in sorted(
        set(bom_by_reference) - schematic_refs - ALLOWED_EXTRA_BOM_REFS
    ):
        errors.append(f"BOM: unknown reference {reference}")

    board = pcbnew.LoadBoard(str(BOARD))
    board.BuildConnectivity()
    footprints = {fp.GetReference(): fp for fp in board.GetFootprints()}
    placed_refs = {
        reference
        for reference, component in components.items()
        if component["footprint"]
    }
    for reference in sorted(placed_refs - set(footprints)):
        errors.append(f"BOARD: missing footprint {reference}")
    for reference in sorted(set(footprints) - placed_refs):
        if not reference.startswith("FID"):
            errors.append(f"BOARD: unexpected footprint {reference}")

    claimed_nodes = set(node_nets) | set(nc_nodes)
    for reference in sorted(placed_refs & set(footprints)):
        footprint = footprints[reference]
        for pad in footprint.Pads():
            pin = pad.GetNumber()
            if not pin:
                continue
            node = (reference, pin)
            expected_net = node_nets.get(node)
            if expected_net is not None and pad.GetNetname() != expected_net:
                errors.append(
                    f"BOARD_PARITY: {reference}.{pin} expected {expected_net}, "
                    f"found {pad.GetNetname() or 'no net'}"
                )
            elif node in nc_nodes and pad.GetNetCode() != 0:
                errors.append(
                    f"BOARD_PARITY: no-connect {reference}.{pin} has {pad.GetNetname()}"
                )
            elif node in BOARD_ONLY_NETS:
                expected_board_net = BOARD_ONLY_NETS[node]
                if pad.GetNetname() != expected_board_net:
                    errors.append(
                        f"BOARD_PARITY: {reference}.{pin} expected "
                        f"{expected_board_net}, found {pad.GetNetname() or 'no net'}"
                    )
            elif node not in claimed_nodes:
                errors.append(f"BOARD_PARITY: unclaimed pad {reference}.{pin}")

    costs = {}
    for quantity in (1, 100, 1000):
        column = f"row_cost_usd_qty{quantity}"
        costs[quantity] = sum(
            float(row[column]) for row in rows if row["fitment"] != "dnp"
        )

    qi_nominal_ma = 262_000 / (845 + 200)
    qi_hardware_ma = 314_000 / (845 + 200)
    charge_ma = 40
    charger_input_ma = 100

    warnings.append(
        f"intentional no-connects: {len(nc_nodes)} "
        f"({sum(1 for node in nc_nodes if node[0] == 'U1')} on U1)"
    )

    print("Design contract (netlist + BOM + board parity)")
    print(f"  nets: {len(real)} real, {len(nc)} no-connect groups, "
          f"{sum(len(v) for v in real.values())} nodes")
    print(f"  pin contracts: {len(PIN_NETS)}")
    print(f"  schematic/BOM references: {len(schematic_refs)}/{len(bom_by_reference)}")
    print(
        "  programmed currents: "
        f"Qi {qi_nominal_ma:.0f} mA nominal/{qi_hardware_ma:.0f} mA hardware, "
        f"charger input {charger_input_ma} mA/charge {charge_ma} mA"
    )
    print(
        "  modeled unit cost: "
        + ", ".join(f"{quantity}={costs[quantity]:.2f} USD" for quantity in costs)
    )
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
