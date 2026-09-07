#!/usr/bin/env python3
"""Generate the inkbot-magsafe KiCad schematic (thickness-first MagSafe e-ink tile).

Follows kenchangh/kicad-schematic: exact pin positions from symbol libraries,
SchematicBuilder.connect_pin (never guess), then kicad-cli netlist validation.
"""

from __future__ import annotations

import json
import math
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOOLS = Path(__file__).resolve().parent / "tools"
sys.path.insert(0, str(TOOLS))

from extract_symbol import embed  # noqa: E402
from kicad_sch_helpers import (  # noqa: E402
    SchematicBuilder,
    SymbolLibrary,
    fix_subsymbol_names,
    lib_sym_power,
    lib_sym_pwr_flag,
    snap,
)

SYM = Path("/usr/share/kicad/symbols")
OUT_DIR = ROOT / "kicad"
OUT = OUT_DIR / "inkbot-magsafe.kicad_sch"
PRO = OUT_DIR / "inkbot-magsafe.kicad_pro"


def build_lib_symbols() -> str:
    return "\n\n".join(
        [
            embed(SYM / "MCU_Nordic.kicad_sym", "MCU_Nordic", "nRF52833_QDxx"),
            embed(SYM / "Battery_Management.kicad_sym", "Battery_Management", "BQ51050BRHL"),
            embed(SYM / "Power_Management.kicad_sym", "Power_Management", "TPS22810DRV"),
            embed(SYM / "Regulator_Linear.kicad_sym", "Regulator_Linear", "MIC5504-3.3YM5"),
            embed(SYM / "Connector_Generic.kicad_sym", "Connector_Generic", "Conn_01x24"),
            embed(SYM / "Connector.kicad_sym", "Connector", "TestPoint"),
            embed(SYM / "Device.kicad_sym", "Device", "Battery_Cell"),
            embed(SYM / "Device.kicad_sym", "Device", "Antenna_Chip"),
            embed(SYM / "Device.kicad_sym", "Device", "Crystal"),
            embed(SYM / "Device.kicad_sym", "Device", "Thermistor_NTC"),
            embed(SYM / "Device.kicad_sym", "Device", "C"),
            embed(SYM / "Device.kicad_sym", "Device", "R"),
            embed(SYM / "Device.kicad_sym", "Device", "L"),
            lib_sym_power("power:GND", "GND"),
            lib_sym_power("power:VSYS", "VSYS"),
            lib_sym_pwr_flag(),
        ]
    )


def pass_v(
    sch: SchematicBuilder,
    lib_id: str,
    ref: str,
    value: str,
    x: float,
    y: float,
    top_net: str,
    bottom_net: str,
    footprint: str = "",
    stub: float = 2.54,
) -> None:
    """Place a vertical 2-pin part and connect by pin number using library coords."""
    sch.place(lib_id, ref, value, x=snap(x), y=snap(y), footprint=footprint)
    sch.connect_pin(ref, "1", top_net, wire_dy=-stub, by_number=True)
    sch.connect_pin(ref, "2", bottom_net, wire_dy=stub, by_number=True)


def main() -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    lib = SymbolLibrary()
    for name in (
        "MCU_Nordic.kicad_sym",
        "Battery_Management.kicad_sym",
        "Power_Management.kicad_sym",
        "Regulator_Linear.kicad_sym",
        "Connector_Generic.kicad_sym",
        "Connector.kicad_sym",
        "Device.kicad_sym",
    ):
        lib.load_from_kicad_sym(str(SYM / name))

    sch = SchematicBuilder(symbol_lib=lib, project_name="inkbot-magsafe")
    sch.set_lib_symbols(build_lib_symbols())

    fp_c0402 = "Capacitor_SMD:C_0402_1005Metric"
    fp_c0603 = "Capacitor_SMD:C_0603_1608Metric"
    fp_c1206 = "Capacitor_SMD:C_1206_3216Metric"
    fp_r0402 = "Resistor_SMD:R_0402_1005Metric"
    fp_l0805 = "Inductor_SMD:L_0805_2012Metric"
    fp_l1210 = "Inductor_SMD:L_1210_3225Metric"

    # --------------------------------------------------------------- Qi power
    # Coil far left; labels go further left so they cannot cross support-part stubs.
    sch.place("Device:L", "L1", "Qi RX coil", x=snap(25), y=snap(40), footprint=fp_l1210)
    sch.connect_pin("L1", "1", "AC1", wire_dx=-10.16, by_number=True)
    sch.connect_pin("L1", "2", "AC2", wire_dx=-10.16, by_number=True)

    qi_x, qi_y = snap(110), snap(75)
    sch.place(
        "Battery_Management:BQ51050BRHL",
        "U5",
        "BQ51050BRHL",
        x=qi_x,
        y=qi_y,
        footprint="Package_DFN_QFN:Texas_VQFN-RHL-20",
    )
    sch.connect_pin("U5", "AC1", "AC1", wire_dx=-10.16)
    sch.connect_pin("U5", "AC2", "AC2", wire_dx=-10.16)
    sch.connect_pin("U5", "BAT", "VSYS", wire_dx=10.16)
    sch.connect_pin("U5", "PGND", "GND", wire_dy=7.62)
    sch.connect_pin("U5", "~{CHG}", "CHG_STAT", wire_dx=7.62)
    sch.connect_pin("U5", "TS/CTRL", "NTC_SENSE", wire_dx=7.62)
    sch.connect_pin("U5", "ILIM", "QI_ILIM", wire_dx=7.62)
    sch.connect_pin("U5", "FOD", "QI_FOD", wire_dx=7.62)
    sch.connect_pin("U5", "TERM", "QI_TERM", wire_dx=7.62)
    sch.connect_pin("U5", "EN2", "GND", wire_dx=5.08)
    sch.connect_pin("U5", "AD", "GND", wire_dx=5.08)
    sch.connect_pin("U5", "RECT", "QI_RECT", wire_dx=10.16)
    for pin, net in (
        ("CLAMP1", "QI_CLAMP1"),
        ("CLAMP2", "QI_CLAMP2"),
        ("COMM1", "QI_COMM1"),
        ("COMM2", "QI_COMM2"),
        ("BOOT1", "QI_BOOT1"),
        ("BOOT2", "QI_BOOT2"),
        ("~{AD-EN}", "QI_AD_EN"),
    ):
        sch.connect_pin("U5", pin, net, wire_dx=-10.16)

    # Support parts in a column well below the coil so stubs cannot cross AC wires.
    pass_v(sch, "Device:C", "C1", "10uF", qi_x + 35, qi_y - 8, "QI_RECT", "GND", fp_c0603)
    pass_v(sch, "Device:C", "C2", "100nF", 55, 110, "AC1", "QI_RECT", fp_c0402)
    pass_v(sch, "Device:C", "C3", "100nF", 65, 110, "AC2", "QI_RECT", fp_c0402)
    pass_v(sch, "Device:C", "C4", "10nF", 55, 130, "QI_BOOT1", "QI_RECT", fp_c0402)
    pass_v(sch, "Device:C", "C5", "10nF", 65, 130, "QI_BOOT2", "QI_RECT", fp_c0402)
    pass_v(sch, "Device:C", "C6", "1uF", 75, 110, "QI_CLAMP1", "QI_RECT", fp_c0402)
    pass_v(sch, "Device:C", "C7", "1uF", 85, 110, "QI_CLAMP2", "QI_RECT", fp_c0402)
    pass_v(sch, "Device:C", "C8", "22nF", 75, 130, "QI_COMM1", "QI_RECT", fp_c0402)
    pass_v(sch, "Device:C", "C9", "22nF", 85, 130, "QI_COMM2", "QI_RECT", fp_c0402)
    pass_v(sch, "Device:R", "R1", "1.1k", qi_x + 40, qi_y + 20, "QI_ILIM", "GND", fp_r0402)
    pass_v(sch, "Device:R", "R2", "20k", qi_x + 50, qi_y + 20, "QI_FOD", "GND", fp_r0402)
    pass_v(sch, "Device:R", "R3", "10k", qi_x + 60, qi_y + 20, "QI_TERM", "GND", fp_r0402)
    pass_v(sch, "Device:R", "R4", "10k", 95, 130, "QI_AD_EN", "QI_RECT", fp_r0402)

    sch.place("Device:Battery_Cell", "BT1", "120mAh LiPo", x=snap(175), y=snap(45), footprint="")
    sch.connect_pin("BT1", "+", "VSYS", wire_dy=-5.08)
    sch.connect_pin("BT1", "-", "GND", wire_dy=5.08)
    pass_v(sch, "Device:C", "C10", "220uF", 190, 45, "VSYS", "GND", fp_c1206)
    pass_v(sch, "Device:C", "C11", "10uF", 200, 45, "VSYS", "GND", fp_c0603)
    pass_v(sch, "Device:Thermistor_NTC", "RT1", "10k", 210, 30, "NTC_SENSE", "GND", fp_r0402)
    pass_v(sch, "Device:R", "R5", "10k", 220, 30, "VSYS", "NTC_SENSE", fp_r0402)
    pass_v(sch, "Device:R", "R6", "100k", 230, 45, "VSYS", "VBAT_SENSE", fp_r0402)
    pass_v(sch, "Device:R", "R7", "100k", 240, 45, "VBAT_SENSE", "GND", fp_r0402)
    pass_v(sch, "Device:R", "R8", "100k", 200, 65, "VSYS", "CHG_STAT", fp_r0402)

    sw_x, sw_y = snap(270), snap(70)
    sch.place(
        "Power_Management:TPS22810DRV",
        "U3",
        "TPS22810DRV",
        x=sw_x,
        y=sw_y,
        footprint="Package_TO_SOT_SMD:SOT-23-6",
    )
    sch.connect_pin("U3", "VIN", "VSYS", wire_dx=-7.62)
    sch.connect_pin("U3", "VOUT", "VSW_PANEL", wire_dx=7.62)
    sch.connect_pin("U3", "EN/UVLO", "PANEL_PWR_EN", wire_dx=-7.62)
    sch.connect_pin("U3", "GND", "GND", wire_dy=5.08)
    sch.connect_pin("U3", "QOD", "GND", wire_dx=5.08)
    sch.connect_pin("U3", "CT", "PANEL_CT", wire_dx=7.62)
    pass_v(sch, "Device:C", "C12", "1nF", sw_x + 22, sw_y + 12, "PANEL_CT", "GND", fp_c0402)

    ldo_x, ldo_y = snap(325), snap(70)
    sch.place(
        "Regulator_Linear:MIC5504-3.3YM5",
        "U4",
        "MIC5504-3.3",
        x=ldo_x,
        y=ldo_y,
        footprint="Package_TO_SOT_SMD:SOT-23-5",
    )
    sch.connect_pin("U4", "VIN", "VSW_PANEL", wire_dx=-7.62)
    sch.connect_pin("U4", "VOUT", "V3V3_PANEL", wire_dx=7.62)
    sch.connect_pin("U4", "GND", "GND", wire_dy=5.08)
    sch.connect_pin("U4", "EN", "VSW_PANEL", wire_dx=-5.08)
    pass_v(sch, "Device:C", "C13", "1uF", ldo_x - 18, ldo_y + 22, "VSW_PANEL", "GND", fp_c0402)
    pass_v(sch, "Device:C", "C14", "1uF", ldo_x + 22, ldo_y + 22, "V3V3_PANEL", "GND", fp_c0402)

    sch.place_pwr_flag(x=snap(185), y=snap(25), net_name="VSYS")
    sch.place_pwr_flag(x=snap(350), y=snap(50), net_name="V3V3_PANEL")
    sch.place_power("power:GND", "GND", snap(175), snap(90))

    # -------------------------------------------------------------------- MCU
    mcu_x, mcu_y = snap(150), snap(230)
    mcu_sym = lib.get("nRF52833_QDxx")
    sch.place(
        "MCU_Nordic:nRF52833_QDxx",
        "U1",
        "nRF52833-QDAA",
        x=mcu_x,
        y=mcu_y,
        footprint="Package_DFN_QFN:Nordic_QFN-40-1EP_5x5mm_P0.4mm",
    )

    # Route each used pin outward from its own symbol coordinate so stub labels
    # never cross the body. Parts below connect to these nets by name.
    pin_nets = {
        "VDD": "VSYS",
        "VDDH": "VSYS",
        "VSS": "GND",
        "VSS_PA": "GND",
        "VBUS": "GND",
        "DCC": "DCC",
        "DEC1": "DEC1",
        "DEC3": "DEC3",
        "DEC4": "DEC4",
        "DEC5": "DEC5",
        "DEC6": "DEC6",
        "DECUSB": "DECUSB",
        "XL1/P0.00": "XL1",
        "XL2/P0.01": "XL2",
        "XC1": "XC1",
        "XC2": "XC2",
        "P0.11": "PANEL_SCLK",
        "P0.15": "PANEL_MOSI",
        "P0.17": "PANEL_CS",
        "P0.20": "PANEL_DC",
        "P1.09": "PANEL_RST",
        "AIN6/P0.30": "PANEL_BUSY",
        "AIN7/P0.31": "PANEL_PWR_EN",
        "AIN0/P0.02": "CHG_STAT",
        "AIN1/P0.03": "VBAT_SENSE",
        "AIN2/P0.04": "NTC_SENSE",
        "SWDIO": "SWDIO",
        "SWDCLK": "SWDCLK",
        "P0.18/~{RESET}": "NRST",
        "ANT": "RF_ANT",
    }
    # Route in the pin's own outward direction (opposite its angle vector) so a
    # stub never crosses the body, regardless of where the symbol origin sits.
    for pin_name, net in pin_nets.items():
        p = mcu_sym.get_pin(pin_name)
        rad = math.radians(p.angle)
        ox, oy = -math.cos(rad), -math.sin(rad)
        if abs(ox) >= abs(oy):
            sch.connect_pin("U1", pin_name, net, wire_dx=(10.16 if ox > 0 else -10.16))
        else:
            sch.connect_pin("U1", pin_name, net, wire_dy=(7.62 if oy > 0 else -7.62))
    for pin in mcu_sym.pins:
        if pin.name not in pin_nets:
            sch.connect_pin_noconnect("U1", pin.name)

    # nRF52833 supply + decoupling (DC/DC on DCC; a cap per DEC rail).
    pass_v(sch, "Device:C", "C15", "100nF", 60, 150, "VSYS", "GND", fp_c0402)
    pass_v(sch, "Device:C", "C16", "4.7uF", 70, 150, "VSYS", "GND", fp_c0603)
    pass_v(sch, "Device:L", "L2", "10uH", 210, 150, "DCC", "VSYS", fp_l0805)
    pass_v(sch, "Device:C", "C17", "100nF", 60, 300, "DEC1", "GND", fp_c0402)
    pass_v(sch, "Device:C", "C18", "100nF", 72, 300, "DEC3", "GND", fp_c0402)
    pass_v(sch, "Device:C", "C19", "100nF", 84, 300, "DEC4", "GND", fp_c0402)
    pass_v(sch, "Device:C", "C20", "100nF", 96, 300, "DEC5", "GND", fp_c0402)
    pass_v(sch, "Device:C", "C23", "100nF", 108, 300, "DEC6", "GND", fp_c0402)
    pass_v(sch, "Device:C", "C24", "1uF", 120, 300, "DECUSB", "GND", fp_c0402)

    sch.place(
        "Device:Crystal",
        "Y1",
        "32.768kHz",
        x=snap(85),
        y=snap(200),
        footprint="Crystal:Crystal_SMD_2012-2Pin_2.0x1.2mm",
    )
    sch.connect_pin("Y1", "1", "XL1", wire_dy=-5.08, by_number=True)
    sch.connect_pin("Y1", "2", "XL2", wire_dy=5.08, by_number=True)

    sch.place(
        "Device:Crystal",
        "Y2",
        "32MHz",
        x=snap(85),
        y=snap(255),
        footprint="Crystal:Crystal_SMD_2012-2Pin_2.0x1.2mm",
    )
    sch.connect_pin("Y2", "1", "XC1", wire_dy=-5.08, by_number=True)
    sch.connect_pin("Y2", "2", "XC2", wire_dy=5.08, by_number=True)

    # 2.4 GHz chip antenna on nRF ANT pin (matching network TBD on layout).
    # No NFC: pairing and frames ride BLE; NFCT pins stay unused (no-connect).
    sch.place(
        "Device:Antenna_Chip",
        "ANT2",
        "2.4GHz",
        x=snap(mcu_x + 80),
        y=snap(mcu_y - 10),
        footprint="Antenna_SMD:Antenna_Abracon_ACA-107-T",
    )
    sch.connect_pin("ANT2", "1", "RF_ANT", wire_dx=-5.08, by_number=True)
    sch.connect_pin("ANT2", "2", "GND", wire_dx=5.08, by_number=True)
    pass_v(sch, "Device:C", "C22", "2.0pF", mcu_x + 75, mcu_y + 15, "RF_ANT", "GND", fp_c0402)

    for i, (net, dy) in enumerate(
        (("SWDIO", 0), ("SWDCLK", 10), ("NRST", 20), ("VSYS", 30), ("GND", 40)),
        start=1,
    ):
        ref = f"TP{i}"
        sch.place(
            "Connector:TestPoint",
            ref,
            "Pad",
            x=snap(mcu_x + 65),
            y=snap(mcu_y + 30 + dy),
            footprint="TestPoint:TestPoint_Pad_D1.5mm",
        )
        sch.connect_pin(ref, "1", net, wire_dx=5.08, by_number=True)

    # ------------------------------------------------------------------ panel
    fpc_x, fpc_y = snap(280), snap(220)
    sch.place(
        "Connector_Generic:Conn_01x24",
        "J1",
        "Panel FPC",
        x=fpc_x,
        y=fpc_y,
        footprint="Connector_FFC-FPC:Hirose_FH12-24S-0.5SH_1x24-1MP_P0.50mm_Horizontal",
    )
    for num, net in {
        "1": "V3V3_PANEL",
        "2": "V3V3_PANEL",
        "3": "GND",
        "4": "GND",
        "5": "PANEL_BUSY",
        "6": "PANEL_RST",
        "7": "PANEL_DC",
        "8": "PANEL_CS",
        "9": "PANEL_SCLK",
        "10": "PANEL_MOSI",
    }.items():
        sch.connect_pin("J1", num, net, wire_dx=-7.62, by_number=True)
    for num in range(11, 25):
        sch.connect_pin_noconnect("J1", str(num))
    pass_v(sch, "Device:C", "C21", "1uF", fpc_x - 28, fpc_y - 45, "V3V3_PANEL", "GND", fp_c0603)

    sch.text_note(
        "inkbot-magsafe MagSafe e-ink tile\\n"
        "nRF52833 QFN-40, BQ51050B Qi+charger, 3.97in 480x800 panel (SSD1677),\\n"
        "0.4 mm PCB, battery in cutout, no case (panel is the front face).",
        snap(15),
        snap(15),
    )

    content = fix_subsymbol_names(
        sch.build(
            title="inkbot-magsafe",
            date="2026-09-06",
            rev="0.4.0",
            paper="A2",
            comments=[
                "Phone-only BLE e-ink tile; detach-to-charge over MagSafe/Qi.",
                "No USB-C. SWD test pads for factory flash and recovery.",
            ],
        )
    )
    OUT.write_text(content)
    print(f"wrote {OUT} ({OUT.stat().st_size} bytes)")

    root_uuid = re.search(r'\(uuid "([^"]+)"\)', content).group(1)
    pro = {
        "board": {
            "design_settings": {
                "defaults": {},
                "diff_pair_dimensions": [],
                "drc_exclusions": [],
                "rules": {
                    "min_clearance": 0.15,
                    "min_track_width": 0.15,
                    "min_via_diameter": 0.4,
                    "min_through_hole_diameter": 0.3,
                },
                "track_widths": [0.15, 0.2, 0.3, 0.5],
                "via_dimensions": [{"diameter": 0.4, "drill": 0.2}],
            },
            "layer_presets": [],
            "viewports": [],
        },
        "boards": [],
        "cvpcb": {"equivalence_files": []},
        "erc": {"erc_exclusions": [], "meta": {"version": 0}, "rule_severities": {}},
        "libraries": {"pinned_footprint_libs": [], "pinned_symbol_libs": []},
        "meta": {"filename": "inkbot-magsafe.kicad_pro", "version": 1},
        "net_settings": {
            "classes": [
                {
                    "bus_width": 12,
                    "clearance": 0.15,
                    "diff_pair_gap": 0.25,
                    "diff_pair_via_gap": 0.25,
                    "diff_pair_width": 0.2,
                    "line_style": 0,
                    "microvia_diameter": 0.3,
                    "microvia_drill": 0.1,
                    "name": "Default",
                    "pcb_color": "rgba(0, 0, 0, 0.000)",
                    "schematic_color": "rgba(0, 0, 0, 0.000)",
                    "track_width": 0.2,
                    "via_diameter": 0.4,
                    "via_drill": 0.2,
                    "wire_width": 6,
                }
            ],
            "meta": {"version": 2},
        },
        "pcbnew": {
            "last_paths": {
                "gencad": "",
                "idf": "",
                "netlist": "",
                "specctra_dsn": "",
                "step": "",
                "vrml": "",
            },
            "page_layout_descr_file": "",
        },
        "schematic": {
            "annotate_start_num": 0,
            "drawing": {
                "default_line_thickness": 6.0,
                "default_text_size": 50.0,
                "field_names": [],
                "intersheets_ref_own_page": False,
                "intersheets_ref_prefix": "",
                "intersheets_ref_short": False,
                "intersheets_ref_show": False,
                "intersheets_ref_suffix": "",
                "junction_size_choice": 3,
                "label_size_ratio": 0.375,
                "pin_symbol_size": 25.0,
                "text_offset_ratio": 0.15,
            },
            "legacy_lib_dir": "",
            "legacy_lib_list": [],
            "meta": {"version": 1},
            "net_format_name": "",
            "page_layout_descr_file": "",
            "plot_directory": "",
            "spice_adjust_passive_values": False,
            "subpart_first_id": 65,
            "subpart_id_separator": 0,
        },
        "sheets": [[root_uuid, "Root"]],
        "text_variables": {},
    }
    PRO.write_text(json.dumps(pro, indent=2) + "\n")
    print(f"wrote {PRO}")


if __name__ == "__main__":
    main()
