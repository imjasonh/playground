#!/usr/bin/env python3
"""Place and route the nfc-eink 4.2 in board.

Phone and coil live on F.Cu. The GDEY042T81 glues to B.Cu. The outline is
91 mm x 77 mm. A 2-turn Class-1 loop sits in the 5 mm bezel; copper pour
stays in the inner island.
"""

from __future__ import annotations

import heapq
import math
import sys
import uuid
from pathlib import Path

import pcbnew

ROOT = Path(__file__).resolve().parents[1]
EMPTY = Path(__file__).resolve().parent / "empty_4layer.kicad_pcb"
OUT = ROOT / "nfc-eink.kicad_pcb"
FP_ROOT = Path("/usr/share/kicad/footprints")

BOARD_W = 91.0
BOARD_H = 77.0
GRID = 0.30
VIA_SIZE = 0.60
VIA_DRILL = 0.30
TRACK = 0.25
PWR_TRACK = 0.40
ANT_TRACK = 0.50

FP = {
    "R0402": (FP_ROOT / "Resistor_SMD.pretty", "R_0402_1005Metric"),
    "C0402": (FP_ROOT / "Capacitor_SMD.pretty", "C_0402_1005Metric"),
    "C0603": (FP_ROOT / "Capacitor_SMD.pretty", "C_0603_1608Metric"),
    "C0805": (FP_ROOT / "Capacitor_SMD.pretty", "C_0805_2012Metric"),
    "CP8": (FP_ROOT / "Capacitor_THT.pretty", "CP_Radial_D8.0mm_P3.50mm"),
    "CP7343": (FP_ROOT / "Capacitor_Tantalum_SMD.pretty", "CP_EIA-7343-20_Kemet-V"),
    "CPSUP": (FP_ROOT / "Capacitor_THT.pretty", "CP_Radial_D12.5mm_P5.00mm"),
    "L4030": (FP_ROOT / "Inductor_SMD.pretty", "L_Coilcraft_XxL4030"),
    "SOD523": (FP_ROOT / "Diode_SMD.pretty", "D_SOD-523"),
    "SOT563": (FP_ROOT / "Package_TO_SOT_SMD.pretty", "SOT-563"),
    "SOT236": (FP_ROOT / "Package_TO_SOT_SMD.pretty", "SOT-23-6"),
    "SOT23": (FP_ROOT / "Package_TO_SOT_SMD.pretty", "SOT-23"),
    "TSSOP8": (FP_ROOT / "Package_SO.pretty", "TSSOP-8_4.4x3mm_P0.65mm"),
    "LQFP48": (FP_ROOT / "Package_QFP.pretty", "LQFP-48_7x7mm_P0.5mm"),
    "FH12": (
        FP_ROOT / "Connector_FFC-FPC.pretty",
        "Hirose_FH12-24S-0.5SH_1x24-1MP_P0.50mm_Horizontal",
    ),
    "SWD": (FP_ROOT / "Connector_PinHeader_1.27mm.pretty", "PinHeader_1x05_P1.27mm_Vertical"),
    "UART": (FP_ROOT / "Connector_PinHeader_2.54mm.pretty", "PinHeader_1x03_P2.54mm_Vertical"),
    "JMP": (FP_ROOT / "Connector_PinHeader_2.54mm.pretty", "PinHeader_1x02_P2.54mm_Vertical"),
}

# ref, footprint key, x, y, rot_deg, value, dnp, pin->net
# Coordinates are millimetres, origin at the SW corner.
PLACES: list[tuple] = [
    ("U1", "TSSOP8", 18.0, 58.0, 0, "NT3H2211W0FTTJ", False, {
        "1": "NFC_LA", "2": "GND", "3": "I2C_SCL", "4": "NFC_FD",
        "5": "I2C_SDA", "6": "+3V3", "7": "VOUT_EH", "8": "NFC_LB",
    }),
    ("U2", "SOT563", 34.0, 48.0, 0, "TPS61023DRLR", False, {
        "1": "BOOST_FB", "2": "VSTORE", "3": "VSTORE", "4": "GND",
        "5": "BOOST_SW", "6": "+3V3",
    }),
    ("U3", "SOT236", 62.0, 36.0, 0, "TPS22917DBVR", False, {
        "1": "+3V3", "2": "GND", "3": "EPD_PWR_EN", "4": "EPD_CT",
        "5": "EPD_QOD", "6": "+3V3_EPD",
    }),
    ("U4", "SOT23", 62.0, 28.0, 0, "TCM809SENB713", False, {
        "1": "GND", "2": "NRST", "3": "+3V3",
    }),
    ("U5", "LQFP48", 46.0, 42.0, 0, "STM32G071CBT6", False, {
        "4": "+3V3", "5": "+3V3", "6": "+3V3", "7": "GND",
        "10": "NRST", "11": "VSTORE_DIV", "13": "DBG_TX", "14": "DBG_RX",
        "15": "EPD_CS", "16": "EPD_SCK", "17": "EPD_BUSY", "18": "EPD_MOSI",
        "19": "EPD_PWR_EN", "28": "EPD_DC", "35": "SWDIO", "36": "SWCLK",
        "37": "EPD_RST", "44": "NFC_FD", "45": "I2C_SCL", "46": "I2C_SDA",
    }),
    ("Q1", "SOT23", 20.0, 28.0, 0, "2N7002", False, {
        "1": "EPD_GDR", "2": "EPD_RESE", "3": "EPD_VGL",
    }),
    ("D1", "SOD523", 24.0, 54.0, 0, "PMEG2010AEB", False, {
        "1": "VHARV_OR", "2": "VOUT_EH",
    }),
    ("L1", "L4030", 42.0, 50.0, 0, "1uH", False, {
        "1": "VSTORE", "2": "BOOST_SW",
    }),
    ("J1", "FH12", 45.5, 10.2, 180, "FH12-24S-0.5SH", False, {
        "2": "EPD_GDR", "3": "EPD_RESE", "5": "EPD_VSH2", "8": "GND",
        "9": "EPD_BUSY", "10": "EPD_RST", "11": "EPD_DC", "12": "EPD_CS",
        "13": "EPD_SCK", "14": "EPD_MOSI", "15": "+3V3_EPD", "16": "+3V3_EPD",
        "17": "GND", "18": "EPD_VDD", "20": "EPD_VSH1", "21": "EPD_VGH",
        "22": "EPD_VSL", "23": "EPD_VGL", "24": "EPD_VCOM",
    }),
    ("J2", "SWD", 80.0, 18.0, 90, "SWD", False, {
        "1": "DBG_3V3", "2": "SWDIO", "3": "SWCLK", "4": "NRST", "5": "GND",
    }),
    ("J3", "UART", 80.0, 30.0, 90, "UART DNP", True, {
        "1": "GND", "2": "DBG_TX", "3": "DBG_RX",
    }),
    ("JP1", "JMP", 80.0, 40.0, 90, "DEBUG_3V3", False, {
        "1": "+3V3", "2": "DBG_3V3",
    }),
    ("C1", "C0402", 22.0, 58.0, 0, "220nF", False, {"1": "VOUT_EH", "2": "GND"}),
    ("C2", "CP7343", 18.0, 20.0, 0, "470uF POSCAP", False, {"1": "VSTORE", "2": "GND"}),
    ("C3", "CPSUP", 74.0, 56.0, 0, "22mF DNP", True, {"1": "VSTORE", "2": "GND"}),
    ("C4", "C0603", 28.0, 48.0, 0, "10uF", False, {"1": "VSTORE", "2": "GND"}),
    ("C5", "C0805", 50.0, 54.0, 0, "22uF", False, {"1": "+3V3", "2": "GND"}),
    ("C6", "C0805", 50.0, 46.0, 0, "22uF", False, {"1": "+3V3", "2": "GND"}),
    ("C7", "C0402", 68.0, 36.0, 0, "1nF", False, {"1": "EPD_CT", "2": "GND"}),
    ("R11", "R0402", 68.0, 32.0, 0, "100k", False, {"1": "EPD_PWR_EN", "2": "GND"}),
    ("R12", "R0402", 68.0, 28.0, 0, "100k", False, {"1": "NRST", "2": "GND"}),
    ("C9", "C0402", 40.0, 36.0, 0, "100nF", False, {"1": "+3V3", "2": "GND"}),
    ("C10", "C0402", 44.0, 36.0, 0, "1uF", False, {"1": "+3V3", "2": "GND"}),
    ("C11", "C0402", 48.0, 36.0, 0, "100nF", False, {"1": "+3V3", "2": "GND"}),
    ("C12", "C0402", 18.0, 16.0, 0, "1uF", False, {"1": "EPD_VDD", "2": "GND"}),
    ("C13", "C0603", 24.0, 16.0, 0, "1uF 25V", False, {"1": "EPD_VGH", "2": "GND"}),
    ("C14", "C0603", 30.0, 16.0, 0, "1uF 25V", False, {"1": "EPD_VGL", "2": "GND"}),
    ("C15", "C0603", 36.0, 16.0, 0, "1uF 25V", False, {"1": "EPD_VSH1", "2": "GND"}),
    ("C16", "C0603", 54.0, 16.0, 0, "1uF 25V", False, {"1": "EPD_VSH2", "2": "GND"}),
    ("C17", "C0603", 60.0, 16.0, 0, "1uF 25V", False, {"1": "EPD_VSL", "2": "GND"}),
    ("C18", "C0603", 66.0, 16.0, 0, "1uF 25V", False, {"1": "EPD_VCOM", "2": "GND"}),
    ("C19", "C0402", 72.0, 16.0, 0, "1uF", False, {"1": "+3V3_EPD", "2": "GND"}),
    ("CT1", "C0402", 10.5, 62.0, 90, "15pF DNP", True, {"1": "NFC_LA", "2": "NFC_LB"}),
    ("CT2", "C0402", 12.5, 62.0, 90, "27pF DNP", True, {"1": "NFC_LA", "2": "NFC_LB"}),
    ("R1", "R0402", 28.0, 54.0, 0, "22", False, {"1": "VHARV_OR", "2": "VSTORE"}),
    ("R2", "R0402", 56.0, 54.0, 0, "453k", False, {"1": "+3V3", "2": "BOOST_FB"}),
    ("R3", "R0402", 56.0, 50.0, 0, "100k", False, {"1": "BOOST_FB", "2": "GND"}),
    ("R4", "R0402", 28.0, 40.0, 0, "220k", False, {"1": "VSTORE", "2": "VSTORE_DIV"}),
    ("R5", "R0402", 28.0, 36.0, 0, "100k", False, {"1": "VSTORE_DIV", "2": "GND"}),
    ("R6", "R0402", 68.0, 40.0, 0, "1k", False, {"1": "EPD_QOD", "2": "+3V3_EPD"}),
    ("R7", "R0402", 38.0, 32.0, 0, "4.7k", False, {"1": "I2C_SCL", "2": "+3V3"}),
    ("R8", "R0402", 42.0, 32.0, 0, "4.7k", False, {"1": "I2C_SDA", "2": "+3V3"}),
    ("R9", "R0402", 46.0, 32.0, 0, "10k", False, {"1": "NFC_FD", "2": "+3V3"}),
    ("R10", "R0402", 24.0, 28.0, 0, "0.47", False, {"1": "EPD_RESE", "2": "GND"}),
]

POWER_NETS = {"GND", "+3V3", "+3V3_EPD", "VSTORE"}
SIGNAL_NETS = {
    "NFC_LA", "NFC_LB", "VOUT_EH", "VHARV_OR", "BOOST_SW", "BOOST_FB",
    "VSTORE_DIV", "EPD_PWR_EN", "EPD_QOD", "EPD_CT", "NRST",
    "I2C_SCL", "I2C_SDA", "NFC_FD", "EPD_CS", "EPD_SCK", "EPD_MOSI",
    "EPD_DC", "EPD_RST", "EPD_BUSY", "EPD_GDR", "EPD_RESE",
    "EPD_VSH1", "EPD_VSH2", "EPD_VGH", "EPD_VGL", "EPD_VSL", "EPD_VCOM",
    "EPD_VDD", "DBG_TX", "DBG_RX", "SWDIO", "SWCLK", "DBG_3V3",
}


def mm(v: float) -> int:
    return int(pcbnew.FromMM(v))


def xy(x: float, y: float) -> pcbnew.VECTOR2I:
    return pcbnew.VECTOR2I(mm(x), mm(y))


def uid() -> str:
    return str(uuid.uuid4())


def get_net(board: pcbnew.BOARD, name: str) -> pcbnew.NETINFO_ITEM:
    found = board.FindNet(name)
    if found is not None and found.GetNetCode() >= 0:
        return found
    item = pcbnew.NETINFO_ITEM(board, name)
    board.Add(item)
    return item


def add_edge(board: pcbnew.BOARD, x1: float, y1: float, x2: float, y2: float) -> None:
    shape = pcbnew.PCB_SHAPE(board)
    shape.SetShape(pcbnew.SHAPE_T_SEGMENT)
    shape.SetStart(xy(x1, y1))
    shape.SetEnd(xy(x2, y2))
    shape.SetLayer(pcbnew.Edge_Cuts)
    shape.SetWidth(mm(0.12))
    board.Add(shape)


def add_text(board: pcbnew.BOARD, text: str, x: float, y: float, layer: int, size: float = 1.0) -> None:
    t = pcbnew.PCB_TEXT(board)
    t.SetText(text)
    t.SetPosition(xy(x, y))
    t.SetLayer(layer)
    t.SetTextSize(pcbnew.VECTOR2I(mm(size), mm(size)))
    t.SetTextThickness(mm(size * 0.15))
    board.Add(t)


def add_track(board: pcbnew.BOARD, net: pcbnew.NETINFO_ITEM, x1: float, y1: float, x2: float, y2: float, layer: int, width: float) -> None:
    if abs(x1 - x2) < 0.01 and abs(y1 - y2) < 0.01:
        return
    tr = pcbnew.PCB_TRACK(board)
    tr.SetStart(xy(x1, y1))
    tr.SetEnd(xy(x2, y2))
    tr.SetWidth(mm(width))
    tr.SetLayer(layer)
    tr.SetNet(net)
    board.Add(tr)


def add_via(board: pcbnew.BOARD, net: pcbnew.NETINFO_ITEM, x: float, y: float) -> None:
    via = pcbnew.PCB_VIA(board)
    via.SetPosition(xy(x, y))
    via.SetWidth(mm(VIA_SIZE))
    via.SetDrill(mm(VIA_DRILL))
    if hasattr(via, "SetLayerPair"):
        via.SetLayerPair(pcbnew.F_Cu, pcbnew.B_Cu)
    via.SetNet(net)
    board.Add(via)


def add_zone(board: pcbnew.BOARD, net: pcbnew.NETINFO_ITEM, layer: int, pts: list[tuple[float, float]], clearance: float = 0.30) -> None:
    zone = pcbnew.ZONE(board)
    zone.SetLayer(layer)
    zone.SetNet(net)
    zone.SetLocalClearance(mm(clearance))
    zone.SetMinThickness(mm(0.25))
    zone.SetThermalReliefGap(mm(0.30))
    zone.SetThermalReliefSpokeWidth(mm(0.30))
    if hasattr(pcbnew, "ZONE_CONNECTION_THERMAL"):
        zone.SetPadConnection(pcbnew.ZONE_CONNECTION_THERMAL)
    outline = zone.Outline()
    outline.NewOutline()
    for x, y in pts:
        outline.Append(mm(x), mm(y))
    board.Add(zone)


def load_fp(key: str) -> pcbnew.FOOTPRINT:
    lib, name = FP[key]
    fp = pcbnew.FootprintLoad(str(lib), name)
    if fp is None:
        raise RuntimeError(f"missing footprint {lib}:{name}")
    return fp


def place_parts(board: pcbnew.BOARD, nets: dict[str, pcbnew.NETINFO_ITEM]) -> dict[str, pcbnew.FOOTPRINT]:
    out: dict[str, pcbnew.FOOTPRINT] = {}
    for ref, fpkey, x, y, rot, value, dnp, pins in PLACES:
        fp = load_fp(fpkey)
        fp.SetReference(ref)
        fp.SetValue(value)
        fp.SetPosition(xy(x, y))
        fp.SetOrientationDegrees(rot)
        fp.SetLayer(pcbnew.F_Cu)
        if dnp and hasattr(fp, "SetDNP"):
            fp.SetDNP(True)
        for pad in fp.Pads():
            n = pins.get(pad.GetNumber())
            if n:
                pad.SetNet(nets[n])
        board.Add(fp)
        out[ref] = fp
    return out


def add_antenna_feed(board: pcbnew.BOARD, nets: dict[str, pcbnew.NETINFO_ITEM]) -> pcbnew.FOOTPRINT:
    fp = pcbnew.FOOTPRINT(board)
    fp.SetReference("ANT1")
    fp.SetValue("PCB loop 2.76uH")
    fp.SetPosition(xy(13.0, 64.0))
    fp.SetLayer(pcbnew.F_Cu)
    for num, dx, net_name in (("1", -1.2, "NFC_LA"), ("2", 1.2, "NFC_LB")):
        pad = pcbnew.PAD(fp)
        pad.SetNumber(num)
        pad.SetName(num)
        pad.SetShape(pcbnew.PAD_SHAPE_RECT)
        pad.SetAttribute(pcbnew.PAD_ATTRIB_SMD)
        pad.SetSize(pcbnew.VECTOR2I(mm(1.2), mm(1.2)))
        pad.SetPosition(xy(13.0 + dx, 64.0))
        layers = pad.GetLayerSet()
        layers.RemoveLayer(pcbnew.B_Cu)
        layers.RemoveLayer(pcbnew.B_Mask)
        layers.RemoveLayer(pcbnew.B_Paste)
        layers.AddLayer(pcbnew.F_Cu)
        layers.AddLayer(pcbnew.F_Mask)
        layers.AddLayer(pcbnew.F_Paste)
        pad.SetLayerSet(layers)
        pad.SetNet(nets[net_name])
        fp.Add(pad)
    board.Add(fp)
    return fp


def antenna_centerline() -> list[tuple[float, float]]:
    # 2-turn spiral, 0.5 mm trace / 0.5 mm gap. Centerline of the outer
    # turn is 1.25 mm from the edge. Feed is on the top edge.
    return [
        (11.8, 64.0),
        (11.8, 75.75),
        (1.25, 75.75),
        (1.25, 1.25),
        (89.75, 1.25),
        (89.75, 75.75),
        (16.2, 75.75),
        (16.2, 74.75),
        (88.75, 74.75),
        (88.75, 2.25),
        (2.25, 2.25),
        (2.25, 74.75),
        (14.2, 74.75),
        (14.2, 64.0),
    ]


def draw_antenna(board: pcbnew.BOARD, nets: dict[str, pcbnew.NETINFO_ITEM]) -> None:
    # The coil is the series path NFC_LA -> NFC_LB. Use NFC_LA for the
    # copper; the two feed pads stitch the ends.
    pts = antenna_centerline()
    net = nets["NFC_LA"]
    for (x1, y1), (x2, y2) in zip(pts, pts[1:]):
        add_track(board, net, x1, y1, x2, y2, pcbnew.F_Cu, ANT_TRACK)
    add_track(board, nets["NFC_LB"], 14.2, 64.0, 14.2, 64.0, pcbnew.F_Cu, ANT_TRACK)


def pad_xy(fp: pcbnew.FOOTPRINT, number: str) -> tuple[float, float]:
    for pad in fp.Pads():
        if pad.GetNumber() == number:
            p = pad.GetPosition()
            return pcbnew.ToMM(p.x), pcbnew.ToMM(p.y)
    raise KeyError(f"{fp.GetReference()} pad {number}")


def is_pth(pad: pcbnew.PAD) -> bool:
    attr = pad.GetAttribute()
    return attr in (pcbnew.PAD_ATTRIB_PTH, getattr(pcbnew, "PAD_ATTRIB_NPTH", -1))


def collect_pads(fps: dict[str, pcbnew.FOOTPRINT]) -> dict[str, list[tuple[float, float, pcbnew.PAD]]]:
    by_net: dict[str, list[tuple[float, float, pcbnew.PAD]]] = {}
    for fp in fps.values():
        for pad in fp.Pads():
            net = pad.GetNetname()
            if not net:
                continue
            p = pad.GetPosition()
            by_net.setdefault(net, []).append((pcbnew.ToMM(p.x), pcbnew.ToMM(p.y), pad))
    return by_net


def stitch_power(board: pcbnew.BOARD, by_net: dict[str, list[tuple[float, float, pcbnew.PAD]]], nets: dict[str, pcbnew.NETINFO_ITEM]) -> None:
    for name in ("GND", "+3V3", "+3V3_EPD", "VSTORE"):
        seen: set[tuple[int, int]] = set()
        for x, y, pad in by_net.get(name, []):
            if is_pth(pad):
                continue
            key = (int(round(x * 10)), int(round(y * 10)))
            if key in seen:
                continue
            seen.add(key)
            # Offset toward the island centre so the via misses the pad.
            cx, cy = BOARD_W / 2, BOARD_H / 2
            dx, dy = cx - x, cy - y
            length = math.hypot(dx, dy) or 1.0
            vx = x + 0.9 * dx / length
            vy = y + 0.9 * dy / length
            add_track(board, nets[name], x, y, vx, vy, pcbnew.F_Cu, PWR_TRACK)
            add_via(board, nets[name], vx, vy)


class Grid:
    def __init__(self, w_mm: float, h_mm: float, step: float):
        self.step = step
        self.nx = int(w_mm / step) + 1
        self.ny = int(h_mm / step) + 1
        self.block = [
            [bytearray(self.ny) for _ in range(self.nx)],
            [bytearray(self.ny) for _ in range(self.nx)],
        ]

    def cell(self, x: float, y: float) -> tuple[int, int]:
        return int(round(x / self.step)), int(round(y / self.step))

    def in_range(self, i: int, j: int) -> bool:
        return 0 <= i < self.nx and 0 <= j < self.ny

    def mark(self, x: float, y: float, r_mm: float, layers: tuple[int, ...] = (0, 1)) -> None:
        i0, j0 = self.cell(x, y)
        rad = max(1, int(math.ceil(r_mm / self.step)))
        for li in layers:
            for di in range(-rad, rad + 1):
                for dj in range(-rad, rad + 1):
                    i, j = i0 + di, j0 + dj
                    if self.in_range(i, j):
                        self.block[li][i][j] = 1

    def mark_rect(self, x0: float, y0: float, x1: float, y1: float, layers: tuple[int, ...] = (0, 1)) -> None:
        ia, ib = self.cell(min(x0, x1), min(y0, y1))
        ic, jd = self.cell(max(x0, x1), max(y0, y1))
        for li in layers:
            for i in range(min(ia, ic), max(ia, ic) + 1):
                for j in range(min(ib, jd), max(ib, jd) + 1):
                    if self.in_range(i, j):
                        self.block[li][i][j] = 1

    def free(self, li: int, i: int, j: int) -> bool:
        return self.in_range(i, j) and self.block[li][i][j] == 0


def seed_obstacles(grid: Grid, fps: dict[str, pcbnew.FOOTPRINT], skip_antenna: bool = False) -> None:
    grid.mark_rect(-1, -1, BOARD_W + 1, 0.35)
    grid.mark_rect(-1, BOARD_H - 0.35, BOARD_W + 1, BOARD_H + 1)
    grid.mark_rect(-1, -1, 0.35, BOARD_H + 1)
    grid.mark_rect(BOARD_W - 0.35, -1, BOARD_W + 1, BOARD_H + 1)
    if not skip_antenna:
        pts = antenna_centerline()
        for (x1, y1), (x2, y2) in zip(pts, pts[1:]):
            steps = max(1, int(math.hypot(x2 - x1, y2 - y1) / grid.step))
            for k in range(steps + 1):
                t = k / steps
                grid.mark(x1 + t * (x2 - x1), y1 + t * (y2 - y1), 0.45, (0,))
    for fp in fps.values():
        for pad in fp.Pads():
            p = pad.GetPosition()
            sx = max(pcbnew.ToMM(pad.GetSize().x), 0.5)
            sy = max(pcbnew.ToMM(pad.GetSize().y), 0.5)
            x, y = pcbnew.ToMM(p.x), pcbnew.ToMM(p.y)
            layers = (0, 1) if is_pth(pad) else (0,)
            grid.mark_rect(
                x - sx / 2 - 0.08,
                y - sy / 2 - 0.08,
                x + sx / 2 + 0.08,
                y + sy / 2 + 0.08,
                layers,
            )


def clear_pad(grid: Grid, x: float, y: float, r_mm: float = 0.7) -> None:
    i0, j0 = grid.cell(x, y)
    rad = max(1, int(math.ceil(r_mm / grid.step)))
    for li in (0, 1):
        for di in range(-rad, rad + 1):
            for dj in range(-rad, rad + 1):
                i, j = i0 + di, j0 + dj
                if grid.in_range(i, j):
                    grid.block[li][i][j] = 0


def astar(grid: Grid, start: tuple[float, float], goal: tuple[float, float]) -> list[tuple[float, float, int]] | None:
    si, sj = grid.cell(start[0], start[1])
    gi, gj = grid.cell(goal[0], goal[1])
    if not grid.in_range(si, sj) or not grid.in_range(gi, gj):
        return None
    clear_pad(grid, start[0], start[1])
    clear_pad(grid, goal[0], goal[1])
    start_state = (si, sj, 1)
    goal_cell = (gi, gj)
    h = lambda i, j: abs(i - gi) + abs(j - gj)
    q: list[tuple[int, int, tuple[int, int, int]]] = [(h(*goal_cell), 0, start_state)]
    came: dict[tuple[int, int, int], tuple[int, int, int] | None] = {start_state: None}
    cost = {start_state: 0}
    moves = ((1, 0), (-1, 0), (0, 1), (0, -1))
    found = None
    while q:
        _, g, (i, j, li) = heapq.heappop(q)
        if (i, j) == goal_cell:
            found = (i, j, li)
            break
        if g != cost.get((i, j, li)):
            continue
        for di, dj in moves:
            ni, nj = i + di, j + dj
            if not grid.free(li, ni, nj) and (ni, nj) != goal_cell:
                continue
            ng = g + 1
            st = (ni, nj, li)
            if ng < cost.get(st, 1_000_000):
                cost[st] = ng
                came[st] = (i, j, li)
                heapq.heappush(q, (ng + h(ni, nj), ng, st))
        # Via to the other layer.
        oi = 1 - li
        if grid.free(oi, i, j) or (i, j) == goal_cell:
            ng = g + 6
            st = (i, j, oi)
            if ng < cost.get(st, 1_000_000):
                cost[st] = ng
                came[st] = (i, j, li)
                heapq.heappush(q, (ng + h(i, j), ng, st))
    if found is None:
        return None
    path = []
    cur: tuple[int, int, int] | None = found
    while cur is not None:
        i, j, li = cur
        path.append((i * grid.step, j * grid.step, li))
        cur = came[cur]
    path.reverse()
    return path


def paint_path(grid: Grid, path: list[tuple[float, float, int]]) -> None:
    for x, y, li in path:
        grid.mark(x, y, 0.28, (li,))


def emit_path(board: pcbnew.BOARD, net: pcbnew.NETINFO_ITEM, path: list[tuple[float, float, int]]) -> None:
    if len(path) < 2:
        return
    # Collapse collinear same-layer runs.
    segs: list[tuple[float, float, float, float, int]] = []
    sx, sy, sl = path[0]
    px, py, pl = path[0]
    for x, y, li in path[1:]:
        if li != sl:
            segs.append((sx, sy, px, py, sl))
            add_via(board, net, px, py)
            sx, sy, sl = px, py, li
        elif (x != px and y != py) and not (x == px or y == py):
            segs.append((sx, sy, px, py, sl))
            sx, sy = px, py
        px, py, pl = x, y, li
    segs.append((sx, sy, px, py, sl))
    layer_of = {0: pcbnew.F_Cu, 1: pcbnew.B_Cu}
    for x1, y1, x2, y2, li in segs:
        add_track(board, net, x1, y1, x2, y2, layer_of[li], TRACK)


def mst_pairs(pts: list[tuple[float, float]]) -> list[tuple[int, int]]:
    n = len(pts)
    if n < 2:
        return []
    used = [False] * n
    used[0] = True
    edges: list[tuple[int, int]] = []
    for _ in range(n - 1):
        best = None
        pair = (0, 1)
        for i in range(n):
            if not used[i]:
                continue
            for j in range(n):
                if used[j]:
                    continue
                d = (pts[i][0] - pts[j][0]) ** 2 + (pts[i][1] - pts[j][1]) ** 2
                if best is None or d < best:
                    best = d
                    pair = (i, j)
        used[pair[1]] = True
        edges.append(pair)
    return edges


def try_l(board: pcbnew.BOARD, net: pcbnew.NETINFO_ITEM, a: tuple[float, float], b: tuple[float, float]) -> None:
    # One-via jog on B.Cu so front-side parts do not block.
    mid = (b[0], a[1])
    add_via(board, net, a[0], a[1])
    add_track(board, net, a[0], a[1], mid[0], mid[1], pcbnew.B_Cu, TRACK)
    add_track(board, net, mid[0], mid[1], b[0], b[1], pcbnew.B_Cu, TRACK)
    add_via(board, net, b[0], b[1])


def route_signals(board: pcbnew.BOARD, fps: dict[str, pcbnew.FOOTPRINT], by_net: dict[str, list[tuple[float, float, pcbnew.PAD]]], nets: dict[str, pcbnew.NETINFO_ITEM]) -> list[str]:
    failed: list[str] = []
    for name in sorted(SIGNAL_NETS):
        pads = by_net.get(name, [])
        if len(pads) < 2:
            continue
        grid = Grid(BOARD_W, BOARD_H, GRID)
        seed_obstacles(grid, fps, skip_antenna=name in {"NFC_LA", "NFC_LB"})
        for x, y, _pad in pads:
            clear_pad(grid, x, y, 0.8)
        pts = [(x, y) for x, y, _ in pads]
        for a, b in mst_pairs(pts):
            path = astar(grid, pts[a], pts[b])
            if path is None:
                try_l(board, nets[name], pts[a], pts[b])
                continue
            emit_path(board, nets[name], path)
            paint_path(grid, path)
    return failed


def connect_antenna_ends(board: pcbnew.BOARD, fps: dict[str, pcbnew.FOOTPRINT], nets: dict[str, pcbnew.NETINFO_ITEM]) -> None:
    la = pad_xy(fps["ANT1"], "1")
    lb = pad_xy(fps["ANT1"], "2")
    add_track(board, nets["NFC_LA"], la[0], la[1], 11.8, 64.0, pcbnew.F_Cu, ANT_TRACK)
    add_track(board, nets["NFC_LB"], lb[0], lb[1], 14.2, 64.0, pcbnew.F_Cu, ANT_TRACK)


def fill_zones(board: pcbnew.BOARD) -> None:
    filler = pcbnew.ZONE_FILLER(board)
    filler.Fill(board.Zones())


def write_empty_copy() -> Path:
    dest = Path("/tmp/nfc-eink-empty.kicad_pcb")
    dest.write_text(EMPTY.read_text())
    return dest


def main() -> int:
    board = pcbnew.LoadBoard(str(write_empty_copy()))
    board.SetCopperLayerCount(4)
    names = sorted(POWER_NETS | SIGNAL_NETS)
    nets = {n: get_net(board, n) for n in names}

    add_edge(board, 0, 0, BOARD_W, 0)
    add_edge(board, BOARD_W, 0, BOARD_W, BOARD_H)
    add_edge(board, BOARD_W, BOARD_H, 0, BOARD_H)
    add_edge(board, 0, BOARD_H, 0, 0)

    fps = place_parts(board, nets)
    fps["ANT1"] = add_antenna_feed(board, nets)
    draw_antenna(board, nets)
    connect_antenna_ends(board, fps, nets)

    # Keep the inner pours smaller than the coil island. A solid plate
    # filling the loop is a shorted turn for 13.56 MHz.
    pour = [(16.0, 22.0), (70.0, 22.0), (70.0, 60.0), (16.0, 60.0)]
    add_zone(board, nets["GND"], pcbnew.In1_Cu, pour, 0.35)
    add_zone(board, nets["+3V3"], pcbnew.In2_Cu, pour, 0.35)
    add_zone(board, nets["GND"], pcbnew.B_Cu, pour, 0.35)
    add_zone(board, nets["+3V3_EPD"], pcbnew.F_Cu, [(16, 8), (74, 8), (74, 18), (16, 18)], 0.30)
    add_zone(board, nets["VSTORE"], pcbnew.F_Cu, [(14, 44), (46, 44), (46, 56), (14, 56)], 0.30)

    by_net = collect_pads(fps)
    stitch_power(board, by_net, nets)
    failed = route_signals(board, fps, by_net, nets)
    fill_zones(board)

    add_text(board, "PHONE / COIL THIS SIDE", 45.5, 66.5, pcbnew.F_SilkS, 1.2)
    add_text(board, "GDEY042T81 PANEL THIS SIDE", 45.5, 66.5, pcbnew.B_SilkS, 1.2)
    add_text(board, "nfc-eink  91x77 mm", 45.5, 22.0, pcbnew.F_SilkS, 0.9)
    add_text(board, "keep phone on coil 8-12 s", 45.5, 24.0, pcbnew.F_SilkS, 0.8)
    add_text(board, "J2 bring-up only. J3 DNP. FPC contacts toward board.", 45.5, 26.0, pcbnew.F_SilkS, 0.7)

    pcbnew.SaveBoard(str(OUT), board)
    print(f"wrote {OUT}")
    if failed:
        print(f"unrouted ({len(failed)}):")
        for line in failed:
            print(f"  {line}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
