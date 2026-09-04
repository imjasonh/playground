#!/usr/bin/env python3
"""Generate the nfc-eink KiCad 7 schematic set."""

from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from kicadlib import (  # noqa: E402
    CUSTOM_IC_LIB,
    Sheet,
    load_custom_lib,
    load_symbol,
)

ROOT = Path(__file__).resolve().parents[1]
PROJECT = "nfc-eink"

FP = {
    "R0402": "Resistor_SMD:R_0402_1005Metric",
    "C0402": "Capacitor_SMD:C_0402_1005Metric",
    "C0603": "Capacitor_SMD:C_0603_1608Metric",
    "C0805": "Capacitor_SMD:C_0805_2012Metric",
    "CP8": "Capacitor_THT:CP_Radial_D8.0mm_P3.50mm",
    "CPSUP": "Capacitor_THT:CP_Radial_D12.5mm_P5.00mm",
    "L4030": "Inductor_SMD:L_Coilcraft_XxL4030",
    "SOD523": "Diode_SMD:D_SOD-523",
    "SOT563": "Package_TO_SOT_SMD:SOT-563",
    "SOT236": "Package_TO_SOT_SMD:SOT-23-6",
    "SOT23": "Package_TO_SOT_SMD:SOT-23",
    "TSSOP8": "Package_SO:TSSOP-8_4.4x3mm_P0.65mm",
    "LQFP48": "Package_QFP:LQFP-48_7x7mm_P0.5mm",
    "FH12": "Connector_FFC-FPC:Hirose_FH12-24S-0.5SH_1x24-1MP_P0.50mm_Horizontal",
    "SWD": "Connector_PinHeader_1.27mm:PinHeader_1x05_P1.27mm_Vertical",
    "UART": "Connector_PinHeader_2.54mm:PinHeader_1x03_P2.54mm_Vertical",
    "JMP": "Connector_PinHeader_2.54mm:PinHeader_1x02_P2.54mm_Vertical",
}


def load_libs():
    r = load_symbol("Device.kicad_sym", "R")
    c = load_symbol("Device.kicad_sym", "C")
    cp = load_symbol("Device.kicad_sym", "C_Polarized")
    l = load_symbol("Device.kicad_sym", "L")
    dsch = load_symbol("Device.kicad_sym", "D_Schottky")
    ant = load_symbol("Device.kicad_sym", "Antenna_Loop")
    gnd = load_symbol("power.kicad_sym", "GND")
    v33 = load_symbol("power.kicad_sym", "+3V3")
    flag = load_symbol("power.kicad_sym", "PWR_FLAG")
    mcu = load_symbol("MCU_ST_STM32G0.kicad_sym", "STM32G071CBTx")
    sw = load_symbol("Power_Management.kicad_sym", "TPS22917DBV")
    sup = load_symbol("Power_Supervisor.kicad_sym", "TCM809")
    fet = load_symbol("Transistor_FET.kicad_sym", "2N7002")
    conn24 = load_symbol("Connector.kicad_sym", "Conn_01x24_Socket")
    conn5 = load_symbol("Connector.kicad_sym", "Conn_01x05_Pin")
    conn3 = load_symbol("Connector.kicad_sym", "Conn_01x03_Pin")
    jmp = load_symbol("Connector.kicad_sym", "Conn_01x02_Pin")
    ntag = load_custom_lib(CUSTOM_IC_LIB, "NT3H2211", "nfc-eink:NT3H2211")
    boost = load_custom_lib(CUSTOM_IC_LIB, "TPS61023", "nfc-eink:TPS61023")

    def clone_rail(value: str, lib_id: str):
        # load_symbol already writes lib_id on the top-level symbol. Only
        # retitle the Value / pin; do not substring-replace power:+3V3 or
        # a second pass turns power:+3V3_EPD into power:+3V3_EPD_EPD.
        sym = load_symbol("power.kicad_sym", "+3V3", lib_id=lib_id)
        sym.raw = re.sub(r'\(property "Value" "\+3V3"', f'(property "Value" "{value}"', sym.raw, count=1)
        sym.raw = re.sub(r'\(name "\+3V3"', f'(name "{value}"', sym.raw)
        # Unit names must keep the same spelling as the symbol name after the colon.
        sym.raw = sym.raw.replace("+3V3_0_1", f"{value}_0_1").replace("+3V3_1_1", f"{value}_1_1")
        # Description mentions +3V3; leave it. ki_description quotes are fine.
        sym.props["Value"] = value
        return sym

    vstore = clone_rail("VSTORE", "power:VSTORE")
    veh = clone_rail("VOUT_EH", "power:VOUT_EH")
    vepd = clone_rail("+3V3_EPD", "power:+3V3_EPD")
    return {
        "R": r,
        "C": c,
        "CP": cp,
        "L": l,
        "D": dsch,
        "ANT": ant,
        "GND": gnd,
        "+3V3": v33,
        "FLAG": flag,
        "MCU": mcu,
        "SW": sw,
        "SUP": sup,
        "FET": fet,
        "J24": conn24,
        "J5": conn5,
        "J3": conn3,
        "J2": jmp,
        "NTAG": ntag,
        "BOOST": boost,
        "VSTORE": vstore,
        "VOUT_EH": veh,
        "+3V3_EPD": vepd,
    }


def two_pin_nets(sheet: Sheet, inst, net1: str, net2: str) -> None:
    nums = [p.number for p in inst.pins]
    sheet.label_pin(inst, nums[0], net1)
    sheet.label_pin(inst, nums[1], net2)


USED_MCU = {
    "10": "NRST",  # PF2-NRST on LQFP48
    "11": "VSTORE_DIV",
    "13": "DBG_TX",
    "14": "DBG_RX",
    "15": "EPD_CS",
    "16": "EPD_SCK",
    "17": "EPD_BUSY",
    "18": "EPD_MOSI",
    "19": "EPD_PWR_EN",
    "28": "EPD_DC",
    "35": "SWDIO",
    "36": "SWCLK",
    "37": "EPD_RST",
    "44": "NFC_FD",
    "45": "I2C_SCL",
    "46": "I2C_SDA",
}

# LQFP48 G071: 4 VBAT, 5 VREF+, 6 VDD, 7 VSS. Pin 10 is PF2-NRST.
POWER_MCU = {"4": "+3V3", "5": "+3V3", "6": "+3V3", "7": "GND"}


def build_root(L) -> Sheet:
    s = Sheet("nfc-eink", "NFC batteryless e-ink tag", "1")
    s.text("NFC batteryless e-ink tag", 20, 20, 4)
    s.text(
        "Recommended design: NT3H2211 (ISO 14443-A harvest + SRAM pass-through)\\n"
        "+ STM32G071CBT6 + TPS61023 + GDEY042T81 4.2 in 400x300.\\n"
        "Phone field powers the board. MCU streams the image, paints the panel, then the rail collapses.",
        20,
        32,
        2,
    )
    s.text(
        "Session: couple phone to the bezel antenna -> harvest charges VSTORE ->\\n"
        "boost reaches 3.3 V -> supervisor releases PF2-NRST -> MCU boots ->\\n"
        "SRAM mailbox drain over I2C -> enable EPD rail -> SSD1683 refresh -> deep sleep / field gone.",
        20,
        52,
        2,
    )
    s.text(
        "Do not hang bulk capacitance on NTAG VOUT. NXP limits that pin to 220 nF.\\n"
        "Charge the tank through R1 (22 ohm) and a Schottky. Keep the phone on the coil for the whole refresh.",
        20,
        72,
        2,
    )
    s.add_child_sheet("NFC front end", "nfc.kicad_sch", 20, 100, 70, 40)
    s.add_child_sheet("Power", "pwr.kicad_sch", 110, 100, 70, 40)
    s.add_child_sheet("MCU", "mcu.kicad_sch", 200, 100, 70, 40)
    s.add_child_sheet("E-paper", "epd.kicad_sch", 290, 100, 70, 40)
    s.text(
        "Board outline equals the GDEY042T81 module (91 mm x 77 mm).\\n"
        "Route a 2-turn Class-1 loop in the bezel; keep copper pour out of the antenna keepout.\\n"
        "See README.md for alternate designs (ST25DV, FM1280 module, 2.13 in, 5.83 in).",
        20,
        160,
        2,
    )
    return s


def build_nfc(L) -> Sheet:
    s = Sheet("nfc", "NFC front end", "2")
    s.text("Antenna and NT3H2211W0FTTJ", 15, 15, 3)
    s.text(
        "Internal Cr = 50 pF. Target Lant = 2.76 uH at 13.56 MHz.\\n"
        "CT1/CT2 are NP0 tuning pads. Leave DNP until a VNA or phone-range sweep.",
        15,
        22,
        1.5,
    )

    ant = s.add(L["ANT"], "ANT1", 40, 80, value="PCB loop 2.76uH")
    s.label_pin(ant, "1", "NFC_LA")
    s.label_pin(ant, "2", "NFC_LB")

    ct1 = s.add(
        L["C"],
        "CT1",
        70,
        60,
        value="15pF NP0 DNP",
        footprint=FP["C0402"],
        dnp=True,
        extra={"MPN": "GRM1555C1H150JA01D"},
    )
    two_pin_nets(s, ct1, "NFC_LA", "NFC_LB")
    ct2 = s.add(
        L["C"],
        "CT2",
        85,
        60,
        value="27pF NP0 DNP",
        footprint=FP["C0402"],
        dnp=True,
        extra={"MPN": "GRM1555C1H270JA01D"},
    )
    two_pin_nets(s, ct2, "NFC_LA", "NFC_LB")

    u = s.add(
        L["NTAG"],
        "U1",
        150,
        90,
        value="NT3H2211W0FTTJ",
        footprint=FP["TSSOP8"],
        extra={"MPN": "NT3H2211W0FTTJ"},
    )
    s.label_pin(u, "1", "NFC_LA")
    s.label_pin(u, "8", "NFC_LB")
    s.label_pin(u, "3", "I2C_SCL")
    s.label_pin(u, "5", "I2C_SDA")
    s.label_pin(u, "4", "NFC_FD", shape="output")
    s.label_pin(u, "7", "VOUT_EH", shape="output")
    s.label_pin(u, "6", "+3V3")
    s.label_pin(u, "2", "GND")

    c1 = s.add(
        L["C"],
        "C1",
        190,
        55,
        value="220nF X7R",
        footprint=FP["C0402"],
        extra={"MPN": "GRM155R71C224KA55D"},
    )
    two_pin_nets(s, c1, "VOUT_EH", "GND")
    s.text("NXP max on VOUT is 220 nF. Do not add more here.", 175, 40, 1.3)

    s.label_pin(s.pwr(L["VOUT_EH"], 220, 80, "VOUT_EH"), "1", "VOUT_EH")
    s.label_pin(s.pwr(L["+3V3"], 220, 100, "+3V3"), "1", "+3V3")
    s.label_pin(s.gnd(L["GND"], 220, 120), "1", "GND")
    return s


def build_pwr(L) -> Sheet:
    s = Sheet("pwr", "Power", "3")
    s.text("Harvest, tank, boost, EPD load switch, reset", 15, 12, 3)

    s.text("VOUT_EH -- D1 -- R1 -- VSTORE -- U2 boost --> +3V3", 15, 22, 1.5)

    d1 = s.add(
        L["D"],
        "D1",
        50,
        55,
        value="PMEG2010AEB",
        footprint=FP["SOD523"],
        extra={"MPN": "PMEG2010AEB,115"},
    )
    # Device:D_Schottky pin 1 is K, pin 2 is A.
    s.label_by_name(d1, "A", "VOUT_EH")
    s.label_by_name(d1, "K", "VHARV_OR")
    r1 = s.add(L["R"], "R1", 80, 55, value="22", footprint=FP["R0402"], extra={"MPN": "RC0402FR-0722RL"})
    two_pin_nets(s, r1, "VHARV_OR", "VSTORE")

    cstore = s.add(
        L["CP"],
        "C2",
        115,
        55,
        value="470uF 6.3V",
        footprint=FP["CP8"],
        extra={"MPN": "6SEPC470M"},
    )
    two_pin_nets(s, cstore, "VSTORE", "GND")
    csuper = s.add(
        L["CP"],
        "C3",
        140,
        55,
        value="22mF 5.5V DNP",
        footprint=FP["CPSUP"],
        dnp=True,
        extra={"MPN": "KR-5R5V223-R"},
    )
    two_pin_nets(s, csuper, "VSTORE", "GND")
    cin = s.add(
        L["C"],
        "C4",
        165,
        55,
        value="10uF 6.3V",
        footprint=FP["C0603"],
        extra={"MPN": "GRM188R60J106ME47D"},
    )
    two_pin_nets(s, cin, "VSTORE", "GND")

    u2 = s.add(
        L["BOOST"],
        "U2",
        80,
        130,
        value="TPS61023DRLR",
        footprint=FP["SOT563"],
        extra={"MPN": "TPS61023DRLR"},
    )
    s.label_pin(u2, "3", "VSTORE")
    s.label_pin(u2, "2", "VSTORE")  # EN to VIN: run whenever the tank is up
    s.label_pin(u2, "4", "GND")
    s.label_pin(u2, "5", "BOOST_SW")
    s.label_pin(u2, "6", "+3V3", shape="output")
    s.label_pin(u2, "1", "BOOST_FB")

    l1 = s.add(L["L"], "L1", 130, 110, value="1uH 3A", footprint=FP["L4030"], extra={"MPN": "XEL4030-102MEB"})
    two_pin_nets(s, l1, "VSTORE", "BOOST_SW")

    rfb1 = s.add(L["R"], "R2", 130, 145, value="453k", footprint=FP["R0402"], extra={"MPN": "RC0402FR-07453KL"})
    two_pin_nets(s, rfb1, "+3V3", "BOOST_FB")
    rfb2 = s.add(L["R"], "R3", 155, 145, value="100k", footprint=FP["R0402"], extra={"MPN": "RC0402FR-07100KL"})
    two_pin_nets(s, rfb2, "BOOST_FB", "GND")
    s.text("Vout = 0.595 x (1 + 453k/100k) = 3.29 V", 175, 145, 1.3)

    cout1 = s.add(
        L["C"],
        "C5",
        190,
        110,
        value="22uF 6.3V",
        footprint=FP["C0805"],
        extra={"MPN": "GRM21BR60J226ME39L"},
    )
    two_pin_nets(s, cout1, "+3V3", "GND")
    cout2 = s.add(
        L["C"],
        "C6",
        215,
        110,
        value="22uF 6.3V",
        footprint=FP["C0805"],
        extra={"MPN": "GRM21BR60J226ME39L"},
    )
    two_pin_nets(s, cout2, "+3V3", "GND")

    s.flag(L["FLAG"], 250, 100)
    s.label_pin(s.symbols[-1], "1", "+3V3")
    s.flag(L["FLAG"], 250, 80)
    s.label_pin(s.symbols[-1], "1", "VSTORE")
    s.flag(L["FLAG"], 250, 60)
    s.label_pin(s.symbols[-1], "1", "+3V3_EPD")

    # ADC divider on the tank.
    rd1 = s.add(L["R"], "R4", 280, 55, value="220k", footprint=FP["R0402"], extra={"MPN": "RC0402FR-07220KL"})
    two_pin_nets(s, rd1, "VSTORE", "VSTORE_DIV")
    rd2 = s.add(L["R"], "R5", 305, 55, value="100k", footprint=FP["R0402"], extra={"MPN": "RC0402FR-07100KL"})
    two_pin_nets(s, rd2, "VSTORE_DIV", "GND")
    s.text("Hold off the EPD rail until VSTORE_DIV says the tank is ready.", 260, 35, 1.3)

    u3 = s.add(
        L["SW"],
        "U3",
        80,
        210,
        value="TPS22917DBVR",
        footprint=FP["SOT236"],
        extra={"MPN": "TPS22917DBVR"},
    )
    s.label_pin(u3, "1", "+3V3")
    s.label_pin(u3, "2", "GND")
    s.label_pin(u3, "3", "EPD_PWR_EN")
    s.label_pin(u3, "6", "+3V3_EPD", shape="output")
    s.label_pin(u3, "5", "EPD_QOD")
    ct = s.add(L["C"], "C7", 130, 200, value="1nF", footprint=FP["C0402"], extra={"MPN": "GRM155R71H102KA01D"})
    two_pin_nets(s, ct, "EPD_CT", "GND")
    s.label_pin(u3, "4", "EPD_CT")
    rq = s.add(L["R"], "R6", 130, 225, value="1k", footprint=FP["R0402"], extra={"MPN": "RC0402FR-071KL"})
    two_pin_nets(s, rq, "EPD_QOD", "+3V3_EPD")

    u4 = s.add(
        L["SUP"],
        "U4",
        200,
        210,
        value="TCM809SENB713",
        footprint=FP["SOT23"],
        extra={"MPN": "TCM809SENB713"},
    )
    s.label_pin(u4, "3", "+3V3")
    s.label_pin(u4, "1", "GND")
    s.label_pin(u4, "2", "NRST", shape="output")
    cnrst = s.add(
        L["C"],
        "C8",
        240,
        210,
        value="100nF",
        footprint=FP["C0402"],
        extra={"MPN": "GRM155R71H104KE14D"},
    )
    two_pin_nets(s, cnrst, "NRST", "GND")
    s.text("2.93 V threshold. Holds PF2-NRST until the boost is in regulation.", 175, 185, 1.3)

    jp = s.add(L["J2"], "JP1", 320, 200, value="DEBUG_3V3", footprint=FP["JMP"])
    s.label_pin(jp, "1", "+3V3")
    s.label_pin(jp, "2", "DBG_3V3")
    s.text("Close JP1 only when an ST-Link feeds J2 pin 1. Leave open for NFC power.", 280, 230, 1.3)

    s.label_pin(s.pwr(L["VSTORE"], 360, 50, "VSTORE"), "1", "VSTORE")
    s.label_pin(s.pwr(L["+3V3"], 360, 70, "+3V3"), "1", "+3V3")
    s.label_pin(s.pwr(L["+3V3_EPD"], 360, 90, "+3V3_EPD"), "1", "+3V3_EPD")
    s.label_pin(s.gnd(L["GND"], 360, 110), "1", "GND")
    s.flag(L["FLAG"], 360, 130)
    s.label_pin(s.symbols[-1], "1", "GND")
    return s


def build_mcu(L) -> Sheet:
    s = Sheet("mcu", "MCU", "4")
    s.text("STM32G071CBT6  (HSI, no crystal)", 15, 12, 3)
    s.text(
        "36 KB RAM holds the 15 000-byte 4.2 in framebuffer.\\n"
        "I2C1 on PB6/PB7. SPI1 on PA5/PA7. PF2 is nRESET on this package.",
        15,
        20,
        1.5,
    )

    u = s.add(
        L["MCU"],
        "U5",
        150,
        130,
        value="STM32G071CBT6",
        footprint=FP["LQFP48"],
        extra={"MPN": "STM32G071CBT6"},
    )
    for num, net in {**USED_MCU, **POWER_MCU}.items():
        shape = "input"
        if num in {"13", "35", "36"}:
            shape = "bidirectional"
        if num in {"13"}:
            shape = "output"
        s.label_pin(u, num, net, shape=shape)
    for p in u.pins:
        if p.number not in USED_MCU and p.number not in POWER_MCU:
            s.nc_pin(u, p.number)

    for ref, x, val in (("C9", 230, "100nF"), ("C10", 255, "1uF"), ("C11", 280, "100nF")):
        mpn = "GRM155R71H104KE14D" if val == "100nF" else "GRM155R61A105KE15D"
        cap = s.add(L["C"], ref, x, 40, value=val, footprint=FP["C0402"], extra={"MPN": mpn})
        two_pin_nets(s, cap, "+3V3", "GND")

    rpu1 = s.add(L["R"], "R7", 230, 70, value="2.2k", footprint=FP["R0402"], extra={"MPN": "RC0402FR-072K2L"})
    two_pin_nets(s, rpu1, "I2C_SCL", "+3V3")
    rpu2 = s.add(L["R"], "R8", 255, 70, value="2.2k", footprint=FP["R0402"], extra={"MPN": "RC0402FR-072K2L"})
    two_pin_nets(s, rpu2, "I2C_SDA", "+3V3")
    rfd = s.add(L["R"], "R9", 280, 70, value="10k", footprint=FP["R0402"], extra={"MPN": "RC0402FR-0710KL"})
    two_pin_nets(s, rfd, "NFC_FD", "+3V3")

    jswd = s.add(L["J5"], "J2", 50, 220, value="SWD", footprint=FP["SWD"])
    # 1 3V3, 2 SWDIO, 3 SWCLK, 4 NRST, 5 GND
    s.label_pin(jswd, "1", "DBG_3V3")
    s.label_pin(jswd, "2", "SWDIO")
    s.label_pin(jswd, "3", "SWCLK")
    s.label_pin(jswd, "4", "NRST")
    s.label_pin(jswd, "5", "GND")
    s.text("J2 1.27 mm: 3V3, SWDIO, SWCLK, NRST, GND", 15, 190, 1.3)

    juart = s.add(L["J3"], "J3", 120, 220, value="UART", footprint=FP["UART"])
    s.label_pin(juart, "1", "GND")
    s.label_pin(juart, "2", "DBG_TX")
    s.label_pin(juart, "3", "DBG_RX")

    s.label_pin(s.pwr(L["+3V3"], 360, 40, "+3V3"), "1", "+3V3")
    s.label_pin(s.gnd(L["GND"], 360, 60), "1", "GND")
    return s


EPD_PINS = {
    "1": None,  # NC
    "2": "EPD_GDR",
    "3": "EPD_RESE",
    "4": None,
    "5": "EPD_VSH2",
    "6": None,  # TSCL unused, we use the on-chip temp sensor
    "7": None,  # TSDA
    "8": "GND",  # BS1 = 4-wire SPI
    "9": "EPD_BUSY",
    "10": "EPD_RST",
    "11": "EPD_DC",
    "12": "EPD_CS",
    "13": "EPD_SCK",
    "14": "EPD_MOSI",
    "15": "+3V3_EPD",  # VDDIO
    "16": "+3V3_EPD",  # VCI
    "17": "GND",
    "18": "EPD_VDD",
    "19": None,  # VPP test
    "20": "EPD_VSH1",
    "21": "EPD_VGH",
    "22": "EPD_VSL",
    "23": "EPD_VGL",
    "24": "EPD_VCOM",
}


def build_epd(L) -> Sheet:
    s = Sheet("epd", "E-paper connector", "5")
    s.text("GDEY042T81  24-pin 0.5 mm FPC  SSD1683", 15, 12, 3)
    s.text(
        "On-glass DC-DC still needs these host capacitors. Typical refresh is 13 mW / 5.6 mA at 3.0 V for 3 s.",
        15,
        22,
        1.5,
    )

    j = s.add(
        L["J24"],
        "J1",
        50,
        140,
        value="FH12-24S-0.5SH",
        footprint=FP["FH12"],
        extra={"MPN": "FH12-24S-0.5SH(55)"},
    )
    for num, net in EPD_PINS.items():
        if net is None:
            s.nc_pin(j, num)
        else:
            s.label_pin(j, num, net)

    # HV reservoir caps. 1uF 25V on the booster rails.
    hv = [
        ("C12", "EPD_VDD", "1uF 6.3V"),
        ("C13", "EPD_VGH", "1uF 25V"),
        ("C14", "EPD_VGL", "1uF 25V"),
        ("C15", "EPD_VSH1", "1uF 25V"),
        ("C16", "EPD_VSH2", "1uF 25V"),
        ("C17", "EPD_VSL", "1uF 25V"),
        ("C18", "EPD_VCOM", "1uF 25V"),
        ("C19", "+3V3_EPD", "1uF 6.3V"),
    ]
    x0 = 140
    for i, (ref, net, val) in enumerate(hv):
        cap = s.add(
            L["C"],
            ref,
            x0 + (i % 4) * 30,
            40 + (i // 4) * 30,
            value=val,
            footprint=FP["C0603"] if "25V" in val else FP["C0402"],
            extra={"MPN": "GRM188R61E105KA12D" if "25V" in val else "GRM155R61A105KE15D"},
        )
        two_pin_nets(s, cap, net, "GND")

    q1 = s.add(L["FET"], "Q1", 200, 160, value="2N7002", footprint=FP["SOT23"], extra={"MPN": "2N7002"})
    s.label_by_name(q1, "G", "EPD_GDR")
    s.label_by_name(q1, "S", "EPD_RESE")
    # SSD1683 typical app: NMOS sits in the VGL pump. Confirm against the panel lot.
    s.label_by_name(q1, "D", "EPD_VGL")
    rs = s.add(L["R"], "R10", 250, 160, value="0.47", footprint=FP["R0402"], extra={"MPN": "RL0402FR-070R47L"})
    two_pin_nets(s, rs, "EPD_RESE", "GND")
    s.text(
        "SSD1683 booster sense MOSFET. Follow Good Display DESPI-C02 if a panel lot already has this on the FPC.",
        160,
        190,
        1.3,
    )

    s.label_pin(s.pwr(L["+3V3_EPD"], 360, 40, "+3V3_EPD"), "1", "+3V3_EPD")
    s.label_pin(s.gnd(L["GND"], 360, 60), "1", "GND")
    return s


def main() -> int:
    L = load_libs()
    (ROOT / "nfc-eink.kicad_sym").write_text(CUSTOM_IC_LIB.strip() + "\n")

    root = build_root(L)
    nfc = build_nfc(L)
    pwr = build_pwr(L)
    mcu = build_mcu(L)
    epd = build_epd(L)

    box = {sh["file"]: sh["uuid"] for sh in root.sheets}
    paths = [
        (f"/{root.uuid}/{box['nfc.kicad_sch']}", "2"),
        (f"/{root.uuid}/{box['pwr.kicad_sch']}", "3"),
        (f"/{root.uuid}/{box['mcu.kicad_sch']}", "4"),
        (f"/{root.uuid}/{box['epd.kicad_sch']}", "5"),
    ]
    root.emit(ROOT / "nfc-eink.kicad_sch", PROJECT, root.uuid, "/", extra_sheet_paths=paths)
    nfc.emit(ROOT / "nfc.kicad_sch", PROJECT, root.uuid, paths[0][0])
    pwr.emit(ROOT / "pwr.kicad_sch", PROJECT, root.uuid, paths[1][0])
    mcu.emit(ROOT / "mcu.kicad_sch", PROJECT, root.uuid, paths[2][0])
    epd.emit(ROOT / "epd.kicad_sch", PROJECT, root.uuid, paths[3][0])
    print(f"wrote schematics in {ROOT}")
    print(f"root uuid {root.uuid}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
