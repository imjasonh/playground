"""KiCad 7 schematic helpers: load symbols, emit sheets, run pin math."""

from __future__ import annotations

import re
import uuid
from dataclasses import dataclass, field
from pathlib import Path

KICAD_SYM = Path("/usr/share/kicad/symbols")


def uid() -> str:
    return str(uuid.uuid4())


def esc(text: str) -> str:
    return text.replace("\\", "\\\\").replace('"', '\\"')


@dataclass
class Pin:
    number: str
    name: str
    etype: str
    x: float
    y: float
    rot: int
    hidden: bool = False


@dataclass
class SymbolDef:
    lib_id: str
    raw: str
    pins: list[Pin]
    props: dict[str, str]


def _extract_balanced(text: str, start: int) -> str:
    depth = 0
    for i in range(start, len(text)):
        if text[i] == "(":
            depth += 1
        elif text[i] == ")":
            depth -= 1
            if depth == 0:
                return text[start : i + 1]
    raise ValueError("unbalanced s-expr")


def _find_symbol_block(text: str, name: str) -> str | None:
    # Match the exact symbol name, not a prefix of a longer name.
    m = re.search(rf'\(symbol "{re.escape(name)}"(?:[\s)])', text)
    if not m:
        return None
    return _extract_balanced(text, m.start())


def _props(block: str) -> dict[str, str]:
    out = {}
    for m in re.finditer(r'\(property "([^"]+)" "([^"]*)"', block):
        out[m.group(1)] = m.group(2)
    return out


def _pins(block: str) -> list[Pin]:
    pins = []
    for m in re.finditer(
        r'\(pin (\w+) \w+ \(at ([-\d.]+) ([-\d.]+) (\d+)\) \(length [-\d.]+\)( hide)?'
        r'[\s\S]*?\(name "([^"]*)"[\s\S]*?\(number "([^"]+)"',
        block,
    ):
        pins.append(
            Pin(
                number=m.group(7),
                name=m.group(6),
                etype=m.group(1),
                x=float(m.group(2)),
                y=float(m.group(3)),
                rot=int(m.group(4)),
                hidden=bool(m.group(5)),
            )
        )
    return pins


def _rename_units(block: str, old: str, new: str) -> str:
    return block.replace(f'(symbol "{old}_', f'(symbol "{new}_')


def load_symbol(lib_file: str, name: str, lib_id: str | None = None) -> SymbolDef:
    text = (KICAD_SYM / lib_file).read_text()
    child = _find_symbol_block(text, name)
    if child is None:
        raise KeyError(f"{lib_file}:{name}")
    props = _props(child)
    parent_name = None
    em = re.search(r'\(extends "([^"]+)"\)', child)
    if em:
        parent_name = em.group(1)
        parent = _find_symbol_block(text, parent_name)
        if parent is None:
            raise KeyError(f"{lib_file} extends {parent_name}")
        # Child properties override; unit graphics come from the parent.
        merged = parent
        for key, val in props.items():
            merged = re.sub(
                rf'\(property "{re.escape(key)}" "[^"]*"',
                f'(property "{key}" "{val}"',
                merged,
                count=1,
            )
        merged = merged.replace(f'(symbol "{parent_name}"', f'(symbol "{name}"', 1)
        merged = _rename_units(merged, parent_name, name)
        block = merged
    else:
        block = child
    lid = lib_id or f"{Path(lib_file).stem}:{name}"
    # Embed under the lib_id KiCad uses in (lib_id ...).
    block = block.replace(f'(symbol "{name}"', f'(symbol "{lid}"', 1)
    block = _rename_units(block, name, lid.replace(":", "_"))
    # Unit names with a colon are invalid; use the original short name for units.
    block = _rename_units(block, lid.replace(":", "_"), name)
    return SymbolDef(lib_id=lid, raw=block, pins=_pins(block), props=_props(block))


def rotate(x: float, y: float, deg: int) -> tuple[float, float]:
    deg %= 360
    if deg == 0:
        return x, y
    if deg == 90:
        return -y, x
    if deg == 180:
        return -x, -y
    if deg == 270:
        return y, -x
    raise ValueError(deg)


@dataclass
class Inst:
    lib_id: str
    ref: str
    value: str
    x: float
    y: float
    rot: int
    footprint: str
    datasheet: str
    pins: list[Pin]
    uuid: str = field(default_factory=uid)
    dnp: bool = False
    extra_props: dict[str, str] = field(default_factory=dict)


class Sheet:
    def __init__(self, name: str, title: str, page: str, paper: str = "A3"):
        self.name = name
        self.title = title
        self.page = page
        self.paper = paper
        self.uuid = uid()
        self.symbols: list[Inst] = []
        self.lib_needed: dict[str, SymbolDef] = {}
        self.wires: list[tuple[float, float, float, float]] = []
        self.junctions: list[tuple[float, float]] = []
        self.labels: list[tuple[str, float, float, int]] = []
        self.glabels: list[tuple[str, float, float, int, str]] = []
        self.noconnects: list[tuple[float, float]] = []
        self.texts: list[tuple[str, float, float, int]] = []
        self.sheets: list[dict] = []
        self._pwr = 0

    def use(self, sym: SymbolDef) -> None:
        self.lib_needed[sym.lib_id] = sym

    def add(self,
        sym: SymbolDef,
        ref: str,
        x: float,
        y: float,
        value: str | None = None,
        rot: int = 0,
        footprint: str | None = None,
        dnp: bool = False,
        extra: dict[str, str] | None = None,
    ) -> Inst:
        self.use(sym)
        inst = Inst(
            lib_id=sym.lib_id,
            ref=ref,
            value=value if value is not None else sym.props.get("Value", ""),
            x=x,
            y=y,
            rot=rot,
            footprint=footprint if footprint is not None else sym.props.get("Footprint", ""),
            datasheet=sym.props.get("Datasheet", ""),
            pins=sym.pins,
            dnp=dnp,
            extra_props=extra or {},
        )
        self.symbols.append(inst)
        return inst

    def pin_xy(self, inst: Inst, number: str) -> tuple[float, float]:
        pin = next(p for p in inst.pins if p.number == str(number))
        px, py = rotate(pin.x, pin.y, inst.rot)
        # Symbol editor +Y is up. Schematic +Y is down.
        return inst.x + px, inst.y - py

    def pin_by_name(self, inst: Inst, name: str) -> Pin:
        for p in inst.pins:
            if p.name == name:
                return p
        raise KeyError(name)

    def wire(self, x1: float, y1: float, x2: float, y2: float) -> None:
        if (x1, y1) != (x2, y2):
            self.wires.append((x1, y1, x2, y2))

    def junc(self, x: float, y: float) -> None:
        self.junctions.append((x, y))

    def gnd(self, gnd_sym: SymbolDef, x: float, y: float) -> Inst:
        self._pwr += 1
        return self.add(gnd_sym, f"#PWR{self._pwr:03d}G", x, y, value="GND")

    def pwr(self, pwr_sym: SymbolDef, x: float, y: float, value: str) -> Inst:
        self._pwr += 1
        return self.add(pwr_sym, f"#PWR{self._pwr:03d}P", x, y, value=value)

    def flag(self, flag_sym: SymbolDef, x: float, y: float) -> Inst:
        self._pwr += 1
        return self.add(flag_sym, f"#FLG{self._pwr:03d}", x, y, value="PWR_FLAG")

    def glabel(self, name: str, x: float, y: float, rot: int = 0, shape: str = "input") -> None:
        self.glabels.append((name, x, y, rot, shape))

    def label_pin(self, inst: Inst, number: str, net: str, shape: str = "input") -> tuple[float, float]:
        x, y = self.pin_xy(inst, number)
        pin = next(p for p in inst.pins if p.number == str(number))
        # Pin orientation is the direction from the connection toward the
        # body, in symbol space. Leave the other way, then Y-flip onto the sheet.
        away = {
            0: (-2.54, 0.0),
            90: (0.0, -2.54),
            180: (2.54, 0.0),
            270: (0.0, 2.54),
        }[pin.rot % 360]
        ax, ay = rotate(away[0], away[1], inst.rot)
        ox, oy = round(x + ax, 2), round(y - ay, 2)
        x, y = round(x, 2), round(y, 2)
        self.wire(x, y, ox, oy)
        dx, dy = ox - x, oy - y
        if abs(dx) >= abs(dy):
            label_rot = 0 if dx > 0 else 180
        else:
            label_rot = 270 if dy > 0 else 90
        self.glabel(net, ox, oy, label_rot, shape)
        return ox, oy

    def label_by_name(self, inst: Inst, name: str, net: str, shape: str = "input") -> tuple[float, float]:
        return self.label_pin(inst, self.pin_by_name(inst, name).number, net, shape)

    def nc_pin(self, inst: Inst, number: str) -> None:
        x, y = self.pin_xy(inst, number)
        self.noconnects.append((x, y))

    def text(self, body: str, x: float, y: float, size: int = 2) -> None:
        self.texts.append((body, x, y, size))

    def add_child_sheet(self, name: str, filename: str, x: float, y: float, w: float, h: float) -> str:
        su = uid()
        self.sheets.append(
            {"name": name, "file": filename, "x": x, "y": y, "w": w, "h": h, "uuid": su}
        )
        return su

    def emit(self,
        path: Path,
        project: str,
        root_uuid: str,
        sheet_path: str,
        extra_sheet_paths: list[tuple[str, str]] | None = None,
    ) -> None:
        lib = "\n".join(
            "\n".join("    " + line if line else "" for line in s.raw.splitlines())
            for s in self.lib_needed.values()
        )
        parts = [
            f'(kicad_sch (version 20230121) (generator eeschema)',
            f'  (uuid {self.uuid})',
            f'  (paper "{self.paper}")',
            f'  (title_block',
            f'    (title "{esc(self.title)}")',
            f'    (date "2026-09-04")',
            f'    (rev "1")',
            f'    (company "playground")',
            f'    (comment 1 "NFC batteryless e-ink tag")',
            f'  )',
            f'  (lib_symbols',
            lib,
            f'  )',
        ]
        for x, y in self.junctions:
            parts.append(f'  (junction (at {x} {y}) (diameter 0) (color 0 0 0 0) (uuid {uid()}))')
        for x, y in self.noconnects:
            parts.append(f'  (no_connect (at {x} {y}) (uuid {uid()}))')
        for x1, y1, x2, y2 in self.wires:
            parts.append(
                f'  (wire (pts (xy {x1} {y1}) (xy {x2} {y2}))'
                f' (stroke (width 0) (type default)) (uuid {uid()}))'
            )
        for name, x, y, rot, shape in self.glabels:
            parts.append(
                f'  (global_label "{esc(name)}"\n'
                f'    (shape {shape})\n'
                f'    (at {x} {y} {rot})\n'
                f'    (fields_autoplaced)\n'
                f'    (effects (font (size 1.27 1.27)) (justify left))\n'
                f'    (uuid {uid()})\n'
                f'    (property "Intersheetrefs" "${{INTERSHEET_REFS}}" (at {x} {y} 0)\n'
                f'      (effects (font (size 1.27 1.27)) hide)))'
            )
        for body, x, y, size in self.texts:
            parts.append(
                f'  (text "{esc(body)}" (at {x} {y} 0)'
                f' (effects (font (size {size} {size})) (justify left bottom))'
                f' (uuid {uid()}))'
            )
        for sh in self.sheets:
            parts.append(
                f'  (sheet (at {sh["x"]} {sh["y"]}) (size {sh["w"]} {sh["h"]})'
                f' (stroke (width 0.1524) (type solid))'
                f' (fill (color 0 0 0 0.0000))'
                f' (uuid {sh["uuid"]})'
                f' (property "Sheet name" "{esc(sh["name"])}" (at {sh["x"]} {sh["y"] - 1.27} 0)'
                f' (effects (font (size 1.27 1.27)) (justify left bottom)))'
                f' (property "Sheet file" "{esc(sh["file"])}" (at {sh["x"]} {sh["y"] + sh["h"] + 1.27} 0)'
                f' (effects (font (size 1.27 1.27)) (justify left top))))'
            )
        for inst in self.symbols:
            dnp = "yes" if inst.dnp else "no"
            pin_uuids = "\n".join(
                f'    (pin "{p.number}" (uuid {uid()}))' for p in inst.pins
            )
            extras = ""
            for k, v in inst.extra_props.items():
                extras += (
                    f'    (property "{esc(k)}" "{esc(v)}" (at {inst.x} {inst.y} 0)'
                    f' (effects (font (size 1.27 1.27)) hide))\n'
                )
            parts.append(
                f'  (symbol (lib_id "{inst.lib_id}") (at {inst.x} {inst.y} {inst.rot}) (unit 1)\n'
                f'    (in_bom yes) (on_board yes) (dnp {dnp})\n'
                f'    (uuid {inst.uuid})\n'
                f'    (property "Reference" "{esc(inst.ref)}" (at {inst.x} {inst.y - 7.62} 0)\n'
                f'      (effects (font (size 1.27 1.27))))\n'
                f'    (property "Value" "{esc(inst.value)}" (at {inst.x} {inst.y + 7.62} 0)\n'
                f'      (effects (font (size 1.27 1.27))))\n'
                f'    (property "Footprint" "{esc(inst.footprint)}" (at {inst.x} {inst.y} 0)\n'
                f'      (effects (font (size 1.27 1.27)) hide))\n'
                f'    (property "Datasheet" "{esc(inst.datasheet)}" (at {inst.x} {inst.y} 0)\n'
                f'      (effects (font (size 1.27 1.27)) hide))\n'
                f'{extras}'
                f'{pin_uuids}\n'
                f'    (instances\n'
                f'      (project "{esc(project)}"\n'
                f'        (path "{sheet_path}"\n'
                f'          (reference "{esc(inst.ref)}") (unit 1)))))'
            )
        parts.append(f'  (sheet_instances')
        parts.append(f'    (path "{sheet_path}" (page "{self.page}"))')
        for pth, page in extra_sheet_paths or []:
            parts.append(f'    (path "{pth}" (page "{page}"))')
        parts.append(f'  )')
        parts.append(f')')
        path.write_text("\n".join(parts) + "\n")


CUSTOM_IC_LIB = r'''
(kicad_symbol_lib (version 20220914) (generator kicad_symbol_editor)
  (symbol "NT3H2211" (in_bom yes) (on_board yes)
    (property "Reference" "U" (at -7.62 10.16 0)
      (effects (font (size 1.27 1.27))))
    (property "Value" "NT3H2211" (at 2.54 10.16 0)
      (effects (font (size 1.27 1.27))))
    (property "Footprint" "Package_SO:TSSOP-8_4.4x3mm_P0.65mm" (at 0 0 0)
      (effects (font (size 1.27 1.27)) hide))
    (property "Datasheet" "https://www.nxp.com/docs/en/data-sheet/NT3H2111_2211.pdf" (at 0 0 0)
      (effects (font (size 1.27 1.27)) hide))
    (property "ki_keywords" "NFC NTAG I2C energy harvest ISO14443" (at 0 0 0)
      (effects (font (size 1.27 1.27)) hide))
    (property "ki_description" "NTAG I2C plus 2K, ISO 14443-A, energy harvest, TSSOP-8" (at 0 0 0)
      (effects (font (size 1.27 1.27)) hide))
    (symbol "NT3H2211_0_1"
      (rectangle (start -7.62 8.89) (end 7.62 -8.89)
        (stroke (width 0.254) (type default)) (fill (type background))))
    (symbol "NT3H2211_1_1"
      (pin passive line (at -10.16 5.08 0) (length 2.54)
        (name "LA" (effects (font (size 1.27 1.27))))
        (number "1" (effects (font (size 1.27 1.27)))))
      (pin power_in line (at 0 -11.43 90) (length 2.54)
        (name "VSS" (effects (font (size 1.27 1.27))))
        (number "2" (effects (font (size 1.27 1.27)))))
      (pin input line (at -10.16 2.54 0) (length 2.54)
        (name "SCL" (effects (font (size 1.27 1.27))))
        (number "3" (effects (font (size 1.27 1.27)))))
      (pin open_collector line (at 10.16 -2.54 180) (length 2.54)
        (name "FD" (effects (font (size 1.27 1.27))))
        (number "4" (effects (font (size 1.27 1.27)))))
      (pin bidirectional line (at -10.16 0 0) (length 2.54)
        (name "SDA" (effects (font (size 1.27 1.27))))
        (number "5" (effects (font (size 1.27 1.27)))))
      (pin power_in line (at 0 11.43 270) (length 2.54)
        (name "VCC" (effects (font (size 1.27 1.27))))
        (number "6" (effects (font (size 1.27 1.27)))))
      (pin power_out line (at 10.16 5.08 180) (length 2.54)
        (name "VOUT" (effects (font (size 1.27 1.27))))
        (number "7" (effects (font (size 1.27 1.27)))))
      (pin passive line (at -10.16 -5.08 0) (length 2.54)
        (name "LB" (effects (font (size 1.27 1.27))))
        (number "8" (effects (font (size 1.27 1.27)))))
    )
  )
  (symbol "TPS61023" (in_bom yes) (on_board yes)
    (property "Reference" "U" (at -7.62 10.16 0)
      (effects (font (size 1.27 1.27))))
    (property "Value" "TPS61023" (at 3.81 10.16 0)
      (effects (font (size 1.27 1.27))))
    (property "Footprint" "Package_TO_SOT_SMD:SOT-563" (at 0 0 0)
      (effects (font (size 1.27 1.27)) hide))
    (property "Datasheet" "https://www.ti.com/lit/ds/symlink/tps61023.pdf" (at 0 0 0)
      (effects (font (size 1.27 1.27)) hide))
    (property "ki_keywords" "boost converter energy harvest" (at 0 0 0)
      (effects (font (size 1.27 1.27)) hide))
    (property "ki_description" "0.5V-start 3.7A boost, SOT-563" (at 0 0 0)
      (effects (font (size 1.27 1.27)) hide))
    (symbol "TPS61023_0_1"
      (rectangle (start -7.62 8.89) (end 7.62 -8.89)
        (stroke (width 0.254) (type default)) (fill (type background))))
    (symbol "TPS61023_1_1"
      (pin input line (at -10.16 -2.54 0) (length 2.54)
        (name "FB" (effects (font (size 1.27 1.27))))
        (number "1" (effects (font (size 1.27 1.27)))))
      (pin input line (at -10.16 0 0) (length 2.54)
        (name "EN" (effects (font (size 1.27 1.27))))
        (number "2" (effects (font (size 1.27 1.27)))))
      (pin power_in line (at -10.16 5.08 0) (length 2.54)
        (name "VIN" (effects (font (size 1.27 1.27))))
        (number "3" (effects (font (size 1.27 1.27)))))
      (pin power_in line (at 0 -11.43 90) (length 2.54)
        (name "GND" (effects (font (size 1.27 1.27))))
        (number "4" (effects (font (size 1.27 1.27)))))
      (pin passive line (at 10.16 5.08 180) (length 2.54)
        (name "SW" (effects (font (size 1.27 1.27))))
        (number "5" (effects (font (size 1.27 1.27)))))
      (pin power_out line (at 10.16 0 180) (length 2.54)
        (name "VOUT" (effects (font (size 1.27 1.27))))
        (number "6" (effects (font (size 1.27 1.27)))))
    )
  )
)
'''


def load_custom_lib(text: str, name: str, lib_id: str) -> SymbolDef:
    block = _find_symbol_block(text, name)
    if block is None:
        raise KeyError(name)
    embedded = block.replace(f'(symbol "{name}"', f'(symbol "{lib_id}"', 1)
    return SymbolDef(lib_id=lib_id, raw=embedded, pins=_pins(embedded), props=_props(embedded))
