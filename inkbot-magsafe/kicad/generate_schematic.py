#!/usr/bin/env python3
"""Generate the corrected inkbot-magsafe KiCad schematic."""

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
LOCAL_SYM = OUT_DIR / "inkbot-magsafe.kicad_sym"
OUT = OUT_DIR / "inkbot-magsafe.kicad_sch"
PRO = OUT_DIR / "inkbot-magsafe.kicad_pro"


def build_lib_symbols() -> str:
    return "\n\n".join(
        [
            embed(SYM / "RF_Module.kicad_sym", "RF_Module", "MDBT50Q-1MV2"),
            embed(LOCAL_SYM, "inkbot_magsafe", "BQ51013C"),
            embed(LOCAL_SYM, "inkbot_magsafe", "BQ25186"),
            embed(LOCAL_SYM, "inkbot_magsafe", "TPS7A2030P"),
            embed(LOCAL_SYM, "inkbot_magsafe", "TPS7A0230P"),
            embed(SYM / "Connector_Generic.kicad_sym", "Connector_Generic", "Conn_01x02"),
            embed(SYM / "Connector_Generic.kicad_sym", "Connector_Generic", "Conn_01x03"),
            embed(SYM / "Connector_Generic.kicad_sym", "Connector_Generic", "Conn_01x04"),
            embed(SYM / "Connector_Generic.kicad_sym", "Connector_Generic", "Conn_01x24"),
            embed(SYM / "Connector.kicad_sym", "Connector", "TestPoint"),
            embed(SYM / "Device.kicad_sym", "Device", "Battery_Cell"),
            embed(SYM / "Device.kicad_sym", "Device", "Crystal"),
            embed(SYM / "Device.kicad_sym", "Device", "Thermistor_NTC"),
            embed(SYM / "Device.kicad_sym", "Device", "C"),
            embed(SYM / "Device.kicad_sym", "Device", "R"),
            embed(SYM / "Device.kicad_sym", "Device", "L"),
            embed(SYM / "Device.kicad_sym", "Device", "D"),
            embed(SYM / "Device.kicad_sym", "Device", "Q_NMOS_GSD"),
            lib_sym_power("power:GND", "GND"),
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
    dnp: bool = False,
) -> None:
    """Place a vertical two-pin part and label both pins."""
    sch.place(
        lib_id,
        ref,
        value,
        x=snap(x),
        y=snap(y),
        footprint=footprint,
        dnp=dnp,
    )
    sch.connect_pin(ref, "1", top_net, wire_dy=-stub, by_number=True)
    sch.connect_pin(ref, "2", bottom_net, wire_dy=stub, by_number=True)


def connect_outward(
    sch: SchematicBuilder,
    symbol,
    ref: str,
    pin: str,
    net: str,
) -> None:
    """Label a pin outside its symbol body."""
    definition = symbol.get_pin_by_number(pin)
    radians = math.radians(definition.angle)
    outward_x = -math.cos(radians)
    outward_y = -math.sin(radians)
    if abs(outward_x) >= abs(outward_y):
        sch.connect_pin(
            ref,
            pin,
            net,
            wire_dx=10.16 if outward_x > 0 else -10.16,
            by_number=True,
        )
    else:
        sch.connect_pin(
            ref,
            pin,
            net,
            wire_dy=7.62 if outward_y > 0 else -7.62,
            by_number=True,
        )


def main() -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    library = SymbolLibrary()
    for name in (
        "RF_Module.kicad_sym",
        "Connector_Generic.kicad_sym",
        "Connector.kicad_sym",
        "Device.kicad_sym",
    ):
        library.load_from_kicad_sym(str(SYM / name))
    library.load_from_kicad_sym(str(LOCAL_SYM))

    sch = SchematicBuilder(symbol_lib=library, project_name="inkbot-magsafe")
    sch.set_lib_symbols(build_lib_symbols())

    c0603 = "Capacitor_SMD:C_0603_1608Metric"
    c0805 = "Capacitor_SMD:C_0805_2012Metric"
    c1206 = "Capacitor_SMD:C_1206_3216Metric"
    r0603 = "Resistor_SMD:R_0603_1608Metric"

    # ---------------------------------------------------- Qi 1.3 receiver
    qi_x, qi_y = snap(92), snap(72)
    sch.place(
        "inkbot_magsafe:BQ51013C",
        "U2",
        "BQ51013C",
        x=qi_x,
        y=qi_y,
        footprint="Package_DFN_QFN:Texas_VQFN-RHL-20",
    )
    for pin, net in {
        "1": "GND",
        "2": "QI_AC1",
        "3": "QI_BOOT1",
        "4": "QI_OUT",
        "5": "QI_CLAMP1",
        "6": "QI_COMM1",
        "7": "QI_PRESENT",
        "9": "GND",
        "10": "QI_EN1",
        "11": "QI_EN2",
        "12": "QI_ILIM",
        "13": "QI_COIL_NTC",
        "14": "QI_FOD",
        "15": "QI_COMM2",
        "16": "QI_CLAMP2",
        "17": "QI_BOOT2",
        "18": "QI_RECT",
        "19": "QI_AC2",
        "20": "GND",
        "21": "GND",
    }.items():
        connect_outward(sch, library.get("BQ51013C"), "U2", pin, net)
    sch.connect_pin_noconnect("U2", "8", by_number=True)

    sch.place(
        "Connector_Generic:Conn_01x04",
        "J3",
        "WR222230 coil + bonded NTC",
        x=snap(25),
        y=snap(45),
        footprint="inkbot_magsafe:Coil_SolderPads",
    )
    sch.connect_pin("J3", "1", "QI_COIL_A", wire_dx=-7.62, by_number=True)
    sch.connect_pin("J3", "2", "QI_AC2", wire_dx=-7.62, by_number=True)
    sch.connect_pin("J3", "3", "QI_COIL_NTC", wire_dx=-7.62, by_number=True)
    sch.connect_pin("J3", "4", "GND", wire_dx=-7.62, by_number=True)
    sch.place("Device:L", "L2", "WR222230-26M8-G 27uH", x=snap(25), y=snap(25))
    sch.connect_pin("L2", "1", "QI_COIL_A", wire_dy=-5.08, by_number=True)
    sch.connect_pin("L2", "2", "QI_AC2", wire_dy=5.08, by_number=True)

    # TI's starting values for the WR222230-26M8-G are 80 nF series and
    # 950 pF parallel. Three C0G parts share the series current. EVT must
    # measure Ls and Ls' in the final stack before freezing these values.
    for ref, value, x in (
        ("C1", "33nF C0G 50V", 42),
        ("C2", "33nF C0G 50V", 50),
        ("C3", "15nF C0G 50V", 58),
    ):
        pass_v(sch, "Device:C", ref, value, x, 70, "QI_COIL_A", "QI_AC1", c0805)
    pass_v(sch, "Device:C", "C4", "820pF C0G 50V", 42, 88, "QI_AC1", "QI_AC2", c0603)
    pass_v(sch, "Device:C", "C5", "130pF C0G 50V", 50, 88, "QI_AC1", "QI_AC2", c0603)
    pass_v(sch, "Device:C", "C6", "10nF 50V", 42, 106, "QI_BOOT1", "QI_AC1", c0603)
    pass_v(sch, "Device:C", "C7", "10nF 50V", 50, 106, "QI_BOOT2", "QI_AC2", c0603)
    pass_v(sch, "Device:C", "C8", "470nF 25V", 58, 106, "QI_CLAMP1", "QI_AC1", c0603)
    pass_v(sch, "Device:C", "C9", "470nF 25V", 66, 106, "QI_CLAMP2", "QI_AC2", c0603)
    pass_v(sch, "Device:C", "C10", "22nF 50V", 74, 106, "QI_COMM1", "QI_AC1", c0603)
    pass_v(sch, "Device:C", "C11", "22nF 50V", 82, 106, "QI_COMM2", "QI_AC2", c0603)
    pass_v(sch, "Device:C", "C12", "10uF 25V", 115, 50, "QI_RECT", "GND", c1206)
    pass_v(sch, "Device:C", "C13", "10uF 25V", 125, 50, "QI_RECT", "GND", c1206)
    pass_v(sch, "Device:C", "C14", "100nF 50V", 135, 50, "QI_RECT", "GND", c0603)
    pass_v(sch, "Device:C", "C15", "10uF 25V", 115, 88, "QI_OUT", "GND", c1206)
    pass_v(sch, "Device:C", "C16", "100nF 50V", 125, 88, "QI_OUT", "GND", c0603)
    pass_v(sch, "Device:R", "R1", "845R 1%", 145, 65, "QI_ILIM", "QI_FOD", r0603)
    pass_v(sch, "Device:R", "R2", "200R 1%", 155, 65, "QI_FOD", "GND", r0603)
    pass_v(sch, "Device:R", "R3", "20k 1%", 145, 88, "QI_RECT", "QI_FOD", r0603)
    pass_v(
        sch,
        "Device:R",
        "R4",
        "DNP",
        155,
        88,
        "QI_OUT",
        "QI_FOD",
        r0603,
        dnp=True,
    )
    pass_v(
        sch,
        "Device:Thermistor_NTC",
        "RT2",
        "103JT-025 10k 3435K film NTC",
        165,
        65,
        "QI_COIL_NTC",
        "GND",
        "",
    )

    # ------------------------------------------------ battery charger and pack
    charger_x, charger_y = snap(205), snap(72)
    sch.place(
        "inkbot_magsafe:BQ25186",
        "U3",
        "BQ25186DLHR",
        x=charger_x,
        y=charger_y,
        footprint="inkbot_magsafe:TI_DLH0010A_WSON-10",
    )
    for pin, net in {
        "1": "SYS",
        "2": "BAT",
        "3": "CHG_PG_N",
        "4": "CHG_CE_N",
        "5": "GND",
        "6": "BAT_NTC",
        "7": "CHG_SDA",
        "8": "CHG_SCL",
        "9": "CHG_INT_N",
        "10": "QI_OUT",
        "11": "GND",
    }.items():
        connect_outward(sch, library.get("BQ25186"), "U3", pin, net)

    pass_v(sch, "Device:C", "C17", "1uF 25V", 180, 45, "QI_OUT", "GND", c0603)
    pass_v(sch, "Device:C", "C18", "10uF 25V", 195, 45, "SYS", "GND", c0805)
    pass_v(sch, "Device:C", "C19", "1uF 10V", 210, 45, "BAT", "GND", c0603)
    pass_v(sch, "Device:R", "R5", "100k", 180, 100, "SYS", "CHG_CE_N", r0603)
    pass_v(sch, "Device:R", "R6", "1M", 195, 100, "CHG_ENABLE", "GND", r0603)
    pass_v(sch, "Device:R", "R7", "10k", 210, 100, "MCU_3V0", "CHG_SDA", r0603)
    pass_v(sch, "Device:R", "R8", "10k", 225, 100, "MCU_3V0", "CHG_SCL", r0603)
    sch.place(
        "Device:Q_NMOS_GSD",
        "Q2",
        "2N7002BK,215",
        x=snap(235),
        y=snap(72),
        footprint="Package_TO_SOT_SMD:SOT-23",
    )
    sch.connect_pin("Q2", "1", "CHG_ENABLE", wire_dx=-5.08, by_number=True)
    sch.connect_pin("Q2", "2", "GND", wire_dy=5.08, by_number=True)
    sch.connect_pin("Q2", "3", "CHG_CE_N", wire_dx=5.08, by_number=True)

    sch.place(
        "Connector_Generic:Conn_01x03",
        "J2",
        "Protected battery + NTC",
        x=snap(270),
        y=snap(55),
        footprint="Connector_Molex:Molex_Pico-EZmate_78171-0003_1x03-1MP_P1.20mm_Vertical",
    )
    for pin, net in {"1": "BAT", "2": "BAT_NTC", "3": "GND"}.items():
        sch.connect_pin("J2", pin, net, wire_dx=7.62, by_number=True)

    sch.place(
        "Device:Battery_Cell",
        "BT1",
        "LP242030 100mAh protected HR",
        x=snap(275),
        y=snap(90),
    )
    sch.connect_pin("BT1", "1", "BAT", wire_dy=-5.08, by_number=True)
    sch.connect_pin("BT1", "2", "GND", wire_dy=5.08, by_number=True)
    pass_v(
        sch,
        "Device:Thermistor_NTC",
        "RT1",
        "10k 3435K bonded to cell",
        295,
        90,
        "BAT_NTC",
        "GND",
        "",
    )

    # ----------------------------------------------------------- BLE module
    module_x, module_y = snap(155), snap(235)
    module = library.get("MDBT50Q-1MV2")
    sch.place(
        "RF_Module:MDBT50Q-1MV2",
        "U1",
        "MDBT50Q-1MV2",
        x=module_x,
        y=module_y,
        footprint="RF_Module:Raytac_MDBT50Q",
    )
    pin_nets = {
        "1": "GND",
        "8": "QI_PRESENT",
        "9": "QI_EN1",
        "10": "SYS_SENSE",
        "11": "PANEL_TEMP_SENSE",
        "12": "PANEL_PWR_EN",
        "14": "PANEL_BUSY",
        "16": "PANEL_TEMP_EXCITE",
        "17": "XL1",
        "18": "XL2",
        "20": "CHG_INT_N",
        "21": "CHG_PG_N",
        "22": "CHG_ENABLE",
        "23": "CHG_SDA",
        "24": "CHG_SCL",
        "25": "QI_EN2",
        "26": "PANEL_RST",
        "27": "PANEL_SCLK",
        "28": "MCU_3V0",
        "30": "MCU_3V0",
        "32": "GND",
        "39": "PANEL_MOSI",
        "40": "NRST",
        "41": "PANEL_CS",
        "44": "PANEL_DC",
        "51": "SWDIO",
        "53": "SWDCLK",
    }
    for pin, net in pin_nets.items():
        connect_outward(sch, module, "U1", pin, net)
    for pin in module.pins:
        if pin.number not in pin_nets:
            sch.connect_pin_noconnect("U1", pin.number, by_number=True)

    # A nanopower 3.0 V LDO keeps the nRF52840 in normal-voltage mode. VDD and
    # VDDH are tied together as the Nordic reference circuit requires.
    sch.place(
        "inkbot_magsafe:TPS7A0230P",
        "U5",
        "TPS7A0230PDBVR",
        x=snap(70),
        y=snap(145),
        footprint="Package_TO_SOT_SMD:SOT-23-5",
    )
    for pin, net in {
        "1": "SYS",
        "2": "GND",
        "3": "SYS",
        "5": "MCU_3V0",
    }.items():
        connect_outward(sch, library.get("TPS7A0230P"), "U5", pin, net)
    sch.connect_pin_noconnect("U5", "4", by_number=True)
    pass_v(sch, "Device:C", "C21", "1uF 10V", 70, 165, "SYS", "GND", c0603)
    pass_v(sch, "Device:C", "C22", "10uF 10V", 82, 165, "MCU_3V0", "GND", c0805)
    sch.place(
        "Device:Crystal",
        "Y1",
        "FC-135 32.768kHz 12.5pF",
        x=snap(105),
        y=snap(175),
        footprint="Crystal:Crystal_SMD_3215-2Pin_3.2x1.5mm",
    )
    sch.connect_pin("Y1", "1", "XL1", wire_dy=-5.08, by_number=True)
    sch.connect_pin("Y1", "2", "XL2", wire_dy=5.08, by_number=True)
    pass_v(sch, "Device:C", "C23", "22pF C0G", 92, 190, "XL1", "GND", c0603)
    pass_v(sch, "Device:C", "C24", "22pF C0G", 105, 190, "XL2", "GND", c0603)

    # The external divider lets SAADC measure SYS while the MCU runs from its
    # regulated rail. Its 1.33 MOhm total resistance draws at most 3.4 uA.
    pass_v(sch, "Device:R", "R9", "1M 1%", 205, 175, "SYS", "SYS_SENSE", r0603)
    pass_v(sch, "Device:R", "R10", "330k 1%", 215, 175, "SYS_SENSE", "GND", r0603)
    pass_v(sch, "Device:C", "C20", "10nF", 220, 190, "SYS_SENSE", "GND", c0603)
    pass_v(
        sch,
        "Device:R",
        "R13",
        "10k 1%",
        235,
        175,
        "PANEL_TEMP_EXCITE",
        "PANEL_TEMP_SENSE",
        r0603,
    )
    pass_v(
        sch,
        "Device:Thermistor_NTC",
        "RT3",
        "NCP18XH103F03RB 10k 3380K",
        245,
        175,
        "PANEL_TEMP_SENSE",
        "GND",
        c0603,
    )

    # C38 stays below the BQ25186's 100 uF maximum SYS capacitance after the
    # other rail capacitors are counted.
    pass_v(sch, "Device:C", "C38", "47uF 10V X5R", 230, 175, "SYS", "GND", c1206)

    # ---------------------------------------------------------- panel power
    ldo_x, ldo_y = snap(285), snap(145)
    sch.place(
        "inkbot_magsafe:TPS7A2030P",
        "U4",
        "TPS7A2030PDBVR",
        x=ldo_x,
        y=ldo_y,
        footprint="Package_TO_SOT_SMD:SOT-23-5",
    )
    for pin, net in {
        "1": "SYS",
        "2": "GND",
        "3": "PANEL_PWR_EN",
        "5": "PANEL_3V0",
    }.items():
        connect_outward(sch, library.get("TPS7A2030P"), "U4", pin, net)
    sch.connect_pin_noconnect("U4", "4", by_number=True)
    pass_v(sch, "Device:C", "C26", "1uF 10V", 265, 160, "SYS", "GND", c0603)
    pass_v(sch, "Device:C", "C27", "100uF 6.3V X5R", 305, 160, "PANEL_3V0", "GND", c1206)

    # ------------------------------------------------------ raw panel + boost
    panel_x, panel_y = snap(345), snap(235)
    sch.place(
        "Connector_Generic:Conn_01x24",
        "J1",
        "GDEY0397T81P panel FPC",
        x=panel_x,
        y=panel_y,
        footprint="Connector_FFC-FPC:Hirose_FH12-24S-0.5SH_1x24-1MP_P0.50mm_Horizontal",
    )
    panel_pins = {
        "2": "PANEL_GDR",
        "3": "PANEL_RESE",
        "5": "PANEL_VSH2",
        "8": "GND",
        "9": "PANEL_BUSY",
        "10": "PANEL_RST",
        "11": "PANEL_DC",
        "12": "PANEL_CS",
        "13": "PANEL_SCLK",
        "14": "PANEL_MOSI",
        "15": "PANEL_3V0",
        "16": "PANEL_3V0",
        "17": "GND",
        "18": "PANEL_VDD",
        "20": "PANEL_VSH1",
        "21": "PANEL_VGH",
        "22": "PANEL_VSL",
        "23": "PANEL_VGL",
        "24": "PANEL_VCOM",
    }
    for pin, net in panel_pins.items():
        sch.connect_pin("J1", pin, net, wire_dx=-7.62, by_number=True)
    for pin in ("1", "4", "6", "7", "19"):
        sch.connect_pin_noconnect("J1", pin, by_number=True)

    pass_v(sch, "Device:C", "C28", "4.7uF 25V", 320, 180, "PANEL_3V0", "GND", c0805)
    pass_v(sch, "Device:C", "C29", "1uF 25V", 330, 180, "PANEL_3V0", "GND", c0603)
    pass_v(sch, "Device:C", "C30", "1uF 50V X5R", 340, 180, "PANEL_VDD", "GND", c0603)
    pass_v(sch, "Device:C", "C31", "4.7uF 35V X7R", 350, 180, "PANEL_VSH2", "GND", c0805)
    pass_v(sch, "Device:C", "C32", "4.7uF 35V X7R", 360, 180, "PANEL_VSH1", "GND", c0805)
    pass_v(sch, "Device:C", "C33", "4.7uF 35V X7R", 370, 180, "PANEL_VGH", "GND", c0805)
    pass_v(sch, "Device:C", "C34", "4.7uF 35V X7R", 380, 180, "PANEL_VSL", "GND", c0805)
    pass_v(sch, "Device:C", "C35", "4.7uF 35V X7R", 390, 180, "PANEL_VGL", "GND", c0805)
    pass_v(sch, "Device:C", "C36", "1uF 50V X5R", 400, 180, "PANEL_VCOM", "GND", c0603)

    sch.place(
        "Device:L",
        "L1",
        "VLS252010CX-100M-1 10uH",
        x=snap(320),
        y=snap(125),
        footprint="inkbot_magsafe:TDK_VLS252010CX",
    )
    sch.connect_pin("L1", "1", "PANEL_3V0", wire_dy=-5.08, by_number=True)
    sch.connect_pin("L1", "2", "PANEL_SW", wire_dy=5.08, by_number=True)
    sch.place(
        "Device:Q_NMOS_GSD",
        "Q1",
        "Si1308EDL-T1-GE3",
        x=snap(345),
        y=snap(125),
        footprint="Package_TO_SOT_SMD:SOT-323_SC-70",
    )
    sch.connect_pin("Q1", "1", "PANEL_GDR", wire_dx=-5.08, by_number=True)
    sch.connect_pin("Q1", "2", "PANEL_RESE", wire_dy=5.08, by_number=True)
    sch.connect_pin("Q1", "3", "PANEL_SW", wire_dx=5.08, by_number=True)
    pass_v(sch, "Device:R", "R11", "2.2R 1%", 335, 145, "PANEL_RESE", "GND", r0603)
    pass_v(sch, "Device:R", "R12", "1M", 350, 145, "PANEL_GDR", "GND", r0603)

    # SSD1677 external positive boost and inverting charge pump, copied from
    # the working Waveshare 3.97-inch board and checked against the panel's
    # GDR/RESE application circuit.
    sch.place("Device:D", "D3", "MBR0530", x=snap(365), y=snap(120), footprint="Diode_SMD:D_SOD-123")
    sch.connect_pin("D3", "2", "PANEL_SW", wire_dx=5.08, by_number=True)
    sch.connect_pin("D3", "1", "PANEL_VGH", wire_dx=-5.08, by_number=True)
    pass_v(sch, "Device:C", "C37", "4.7uF 35V X7R", 375, 135, "PANEL_SW", "PANEL_PUMP", c0805)
    sch.place("Device:D", "D2", "MBR0530", x=snap(390), y=snap(120), footprint="Diode_SMD:D_SOD-123")
    sch.connect_pin("D2", "2", "PANEL_PUMP", wire_dx=5.08, by_number=True)
    sch.connect_pin("D2", "1", "GND", wire_dx=-5.08, by_number=True)
    sch.place("Device:D", "D1", "MBR0530", x=snap(390), y=snap(145), footprint="Diode_SMD:D_SOD-123")
    sch.connect_pin("D1", "2", "PANEL_VGL", wire_dx=5.08, by_number=True)
    sch.connect_pin("D1", "1", "PANEL_PUMP", wire_dx=-5.08, by_number=True)
    # ------------------------------------------------------------ test access
    for index, (net, x, y) in enumerate(
        (
            ("SWDIO", 240, 245),
            ("SWDCLK", 252, 245),
            ("NRST", 264, 245),
            ("MCU_3V0", 276, 245),
            ("GND", 288, 245),
            ("SYS", 240, 263),
            ("BAT", 252, 263),
            ("QI_OUT", 264, 263),
            ("PANEL_3V0", 276, 263),
        ),
        start=1,
    ):
        ref = f"TP{index}"
        sch.place(
            "Connector:TestPoint",
            ref,
            net,
            x=snap(x),
            y=snap(y),
            footprint="TestPoint:TestPoint_Pad_D1.0mm",
        )
        sch.connect_pin(ref, "1", net, wire_dy=5.08, by_number=True)

    sch.place_power("power:GND", "GND", snap(205), snap(120))

    sch.text_note(
        "inkbot-magsafe EVT schematic\\n"
        "BQ51013C Qi 1.3 receiver + BQ25186 protected-cell charger,\\n"
        "Raytac MDBT50Q-1MV2 on a nanopower 3.0 V rail, and the GDEY0397T81P\\n"
        "SSD1677 boost circuit. Qi resonance and FOD values require EVT tuning.",
        snap(15),
        snap(15),
    )

    content = fix_subsymbol_names(
        sch.build(
            title="inkbot-magsafe",
            date="2026-09-07",
            rev="0.8.0",
            paper="A2",
            comments=[
                "EVT design. Do not release until coil tuning, FOD, thermal, and compliance gates pass.",
                "No USB port. SWD pads provide factory programming and recovery.",
            ],
        )
    )
    OUT.write_text(content)
    print(f"wrote {OUT} ({OUT.stat().st_size} bytes)")

    root_uuid = re.search(r'\(uuid "([^"]+)"\)', content).group(1)
    project = {
        "board": {
            "design_settings": {
                "defaults": {
                    "copper_edge_clearance": 0.5,
                    "copper_line_width": 0.1,
                    "courtyard_line_width": 0.05,
                    "edge_cuts_line_width": 0.05,
                    "silk_line_width": 0.15,
                    "silk_text_size_h": 1.0,
                    "silk_text_size_v": 1.0,
                    "silk_text_thickness": 0.15,
                },
                "diff_pair_dimensions": [],
                "drc_exclusions": [],
                "rules": {
                    "min_clearance": 0.1,
                    "min_copper_edge_clearance": 0.5,
                    "min_hole_clearance": 0.2,
                    "min_hole_to_hole": 0.2,
                    "min_track_width": 0.1,
                    "min_via_annular_width": 0.1,
                    "min_via_diameter": 0.45,
                    "min_through_hole_diameter": 0.2,
                },
                "track_widths": [0.1, 0.12, 0.15, 0.2, 0.3, 0.5],
                "via_dimensions": [
                    {"diameter": 0.45, "drill": 0.2},
                    {"diameter": 0.5, "drill": 0.25},
                ],
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
                    "clearance": 0.1,
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
                    "via_diameter": 0.5,
                    "via_drill": 0.25,
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
            "spice_adjust_passive_values": False,
            "subpart_first_id": 65,
            "subpart_id_separator": 0,
        },
        "sheets": [[root_uuid, "Root"]],
        "text_variables": {},
    }
    PRO.write_text(json.dumps(project, indent=2) + "\n")
    print(f"wrote {PRO}")


if __name__ == "__main__":
    main()
