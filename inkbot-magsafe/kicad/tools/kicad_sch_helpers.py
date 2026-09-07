#!/usr/bin/env python3
"""
KiCad Schematic Helper Library — v3 (battle-tested, KiCad 8 + 9)

Provides reliable, computed coordinate transforms and S-expression generation
for KiCad 8/9 .kicad_sch files. Also provides utilities for fixing ERC errors
on existing schematics and handling KiCad 8→9 migration.

TWO MODES OF OPERATION:
  A. Generating new schematics: SchematicBuilder, SymbolLibrary, pin_abs, snap
  B. Fixing existing schematics: find_block, remove_by_uuid, replace_lib_id,
     fix_annotation_suffixes, create_pwr_flag_block, etc.

LESSONS LEARNED from real-world debugging:
1. NEVER guess pin positions — always compute from symbol definitions
2. ALL coordinates must be snapped to 1.27mm grid (snap() everything)
3. Sub-symbols in lib_symbols must NOT have library prefix (Device:R_0_1 → R_0_1)
4. Labels must be at EXACT pin positions or connected via wires
5. PWR_FLAG needed on every power output net (voltage regulator outputs)
6. SOT-23-5 LDOs: VOUT is at (7.62, 2.54), NC is at (7.62, -2.54) — don't mix them up!
7. Every pin must be either: wired+labeled, connected to power, or have no_connect flag
8. Don't replace embedded Device:C/R/L with KiCad 9 versions (pin positions changed)
9. kicad-cli JSON goes to file (-o flag), not stdout — never pipe to python
10. CLI ERC doesn't check annotations — KiCad 9 GUI requires refs ending in digits

Usage (generating):
    from kicad_sch_helpers import SchematicBuilder, SymbolLibrary, snap, pin_abs

Usage (fixing):
    from kicad_sch_helpers import (find_block, remove_by_uuid, replace_lib_id,
        replace_footprint, fix_annotation_suffixes, create_pwr_flag_block, run_erc)

The key insight: KiCad symbol libraries use Y-up (math convention),
but .kicad_sch files use Y-down (screen convention). When placing a
symbol at (sx, sy), a pin defined at library position (px, py) maps
to schematic position using:

    Rotation 0:   (sx + px, sy - py)
    Rotation 90:  (sx + py, sy + px)
    Rotation 180: (sx - px, sy + py)
    Rotation 270: (sx - py, sy - px)

This library handles all of this automatically via pin_abs().
"""

import uuid as _uuid
import re
import json
import subprocess
import sys
from pathlib import Path
from dataclasses import dataclass
from typing import Optional


# =============================================================================
# Grid and coordinate utilities
# =============================================================================

GRID = 1.27  # KiCad default schematic grid in mm (50 mil)


def snap(v: float) -> float:
    """Snap a coordinate to the nearest 1.27mm grid point.
    ALWAYS use this for every coordinate in the schematic."""
    return round(v / GRID) * GRID


def uid() -> str:
    """Generate a UUID for KiCad elements."""
    return str(_uuid.uuid4())


def pin_transform(pin_x: float, pin_y: float, rotation: int = 0) -> tuple:
    """
    Transform a pin position from library space to schematic offset space.

    In library space: Y-up (positive Y = up on screen)
    In schematic space: Y-down (positive Y = down on screen)

    Args:
        pin_x, pin_y: Pin position in library (symbol) coordinates
        rotation: Symbol rotation in degrees (0, 90, 180, 270)

    Returns:
        (dx, dy): Offset to add to symbol placement position
    """
    transforms = {
        0:   ( pin_x, -pin_y),
        90:  ( pin_y,  pin_x),
        180: (-pin_x,  pin_y),
        270: (-pin_y, -pin_x),
    }
    if rotation not in transforms:
        raise ValueError(f"Rotation must be 0, 90, 180, or 270. Got {rotation}")
    return transforms[rotation]


def pin_abs(sx: float, sy: float, px: float, py: float,
            rotation: int = 0, mirror_y: bool = False) -> tuple:
    """
    Compute absolute schematic position of a pin. THE key function.

    Args:
        sx, sy: Symbol placement position in schematic (should be grid-snapped)
        px, py: Pin position in library (symbol) coordinates
        rotation: Symbol rotation (0, 90, 180, 270)
        mirror_y: Whether symbol is Y-mirrored

    Returns:
        (abs_x, abs_y): Absolute pin position, grid-snapped

    Example:
        # AD9363 at (320, 200), TX1A_P pin at library (-17.78, 25.40)
        x, y = pin_abs(320, 200, -17.78, 25.40)
        # Returns (302.26, 174.63) — snapped to grid
    """
    if mirror_y:
        px = -px

    dx, dy = pin_transform(px, py, rotation)
    return (snap(sx + dx), snap(sy + dy))


# =============================================================================
# Symbol library parser
# =============================================================================

@dataclass
class PinDef:
    """A pin definition from a symbol library."""
    name: str
    number: str
    x: float
    y: float
    angle: int
    length: float
    pin_type: str  # passive, power_in, power_out, input, output, bidirectional


@dataclass
class SymbolDef:
    """A symbol definition with its pins."""
    name: str
    pins: list  # List[PinDef]

    def get_pin(self, name: str) -> Optional[PinDef]:
        """Get pin by name."""
        for p in self.pins:
            if p.name == name:
                return p
        return None

    def get_pin_by_name(self, name: str) -> Optional[PinDef]:
        """Get pin by name (alias for get_pin)."""
        return self.get_pin(name)

    def get_pin_by_number(self, number: str) -> Optional[PinDef]:
        """Get pin by number string."""
        for p in self.pins:
            if p.number == number:
                return p
        return None

    def pin_pos(self, name: str) -> tuple:
        """Get (x, y) library position of a pin by name. Raises if not found."""
        p = self.get_pin(name)
        if not p:
            raise KeyError(f"Pin '{name}' not found in symbol '{self.name}'. "
                          f"Available: {[pin.name for pin in self.pins]}")
        return (p.x, p.y)


class SymbolLibrary:
    """
    Parse and store symbol definitions from .kicad_sym files
    or from the lib_symbols section of a .kicad_sch file.

    Usage:
        lib = SymbolLibrary()
        lib.load_from_kicad_sym("path/to/library.kicad_sym")
        ad9363 = lib.get("AD9363ABCZ")
        px, py = ad9363.pin_pos("TX1A_P")
    """

    def __init__(self):
        self.symbols: dict = {}  # name -> SymbolDef

    def load_from_kicad_sym(self, filepath: str):
        """Load symbols from a .kicad_sym library file."""
        with open(filepath) as f:
            content = f.read()
        self._parse(content)

    # Keep 'load' as alias for backward compatibility
    load = load_from_kicad_sym

    def _parse(self, content: str):
        """Parse symbol definitions from S-expression content."""
        pin_pattern = re.compile(
            r'\(pin\s+(\w+)\s+\w+\s+'
            r'\(at\s+([-\d.]+)\s+([-\d.]+)\s+(\d+)\)\s+'
            r'\(length\s+([-\d.]+)\)(?:\s+hide)?\s+'
            r'\(name\s+"([^"]*)".*?\)\s+'
            r'\(number\s+"([^"]*)".*?\)\)',
            re.DOTALL
        )

        lines = content.split('\n')
        i = 0
        while i < len(lines):
            line = lines[i].strip()
            m = re.match(r'^\(symbol\s+"([^"]+)"', line)
            # Skip sub-symbols (those ending in _digit_digit)
            if m and not re.search(r'_\d+_\d+$', m.group(1)):
                sym_name = m.group(1)
                depth = line.count('(') - line.count(')')
                block_lines = [line]
                j = i + 1
                while j < len(lines) and depth > 0:
                    l = lines[j].strip()
                    depth += l.count('(') - l.count(')')
                    block_lines.append(l)
                    j += 1

                block = '\n'.join(block_lines)
                pins = []
                for pm in pin_pattern.finditer(block):
                    pins.append(PinDef(
                        name=pm.group(6), number=pm.group(7),
                        x=float(pm.group(2)), y=float(pm.group(3)),
                        angle=int(pm.group(4)), length=float(pm.group(5)),
                        pin_type=pm.group(1),
                    ))
                if pins:
                    self.symbols[sym_name] = SymbolDef(name=sym_name, pins=pins)
                i = j
            else:
                i += 1

    def get(self, name: str) -> Optional[SymbolDef]:
        """Get symbol by name (tries with and without library prefix)."""
        if name in self.symbols:
            return self.symbols[name]
        if ':' in name:
            short = name.split(':', 1)[1]
            if short in self.symbols:
                return self.symbols[short]
        return None


# =============================================================================
# lib_symbols template generators
# =============================================================================

def lib_sym_2pin(lib_id: str, ref_prefix: str, default_val: str,
                 pin1_name: str = "1", pin2_name: str = "2",
                 pin1_type: str = "passive", pin2_type: str = "passive",
                 body: str = "rect") -> str:
    """
    Generate lib_symbol for a 2-pin component.

    IMPORTANT: Sub-symbol names use ONLY the symbol name, not the library prefix.
    This is handled automatically by this function.

    Standard 2-pin pin positions:
        Pin 1: (0, 2.54) pointing down (angle 270) — TOP in schematic
        Pin 2: (0, -2.54) pointing up (angle 90) — BOTTOM in schematic
    """
    sym_name = lib_id.split(':')[-1] if ':' in lib_id else lib_id

    bodies = {
        "rect": """      (rectangle (start -1.016 1.27) (end 1.016 -1.27)
        (stroke (width 0.254) (type default)) (fill (type none)))""",
        "cap": """      (polyline (pts (xy -1.27 0.508) (xy 1.27 0.508))
        (stroke (width 0.254) (type default)) (fill (type none)))
      (polyline (pts (xy -1.27 -0.508) (xy 1.27 -0.508))
        (stroke (width 0.254) (type default)) (fill (type none)))""",
        "inductor": """      (arc (start 0 -1.27) (mid 0.635 -0.635) (end 0 0)
        (stroke (width 0.254) (type default)) (fill (type none)))
      (arc (start 0 0) (mid 0.635 0.635) (end 0 1.27)
        (stroke (width 0.254) (type default)) (fill (type none)))""",
        "diode": """      (polyline (pts (xy -1.27 1.016) (xy -1.27 -1.016) (xy 1.27 0) (xy -1.27 1.016))
        (stroke (width 0.254) (type default)) (fill (type none)))
      (polyline (pts (xy 1.27 1.016) (xy 1.27 -1.016))
        (stroke (width 0.254) (type default)) (fill (type none)))""",
        "led": """      (polyline (pts (xy -1.27 1.016) (xy -1.27 -1.016) (xy 1.27 0) (xy -1.27 1.016))
        (stroke (width 0.254) (type default)) (fill (type none)))
      (polyline (pts (xy 1.27 1.016) (xy 1.27 -1.016))
        (stroke (width 0.254) (type default)) (fill (type none)))""",
    }
    drawing = bodies.get(body, bodies["rect"])

    return f"""    (symbol "{lib_id}"
      (pin_numbers hide) (pin_names hide) (in_bom yes) (on_board yes)
      (property "Reference" "{ref_prefix}" (at 2.54 0.508 0)
        (effects (font (size 1.27 1.27)) (justify left)))
      (property "Value" "{default_val}" (at 2.54 -1.016 0)
        (effects (font (size 1.27 1.27)) (justify left)))
      (property "Footprint" "" (at 0 0 0)
        (effects (font (size 1.27 1.27)) hide))
      (symbol "{sym_name}_0_1"
{drawing}
      )
      (symbol "{sym_name}_1_1"
        (pin {pin1_type} line (at 0 2.54 270) (length 1.27)
          (name "{pin1_name}" (effects (font (size 1.0 1.0))))
          (number "1" (effects (font (size 1.0 1.0)))))
        (pin {pin2_type} line (at 0 -2.54 90) (length 1.27)
          (name "{pin2_name}" (effects (font (size 1.0 1.0))))
          (number "2" (effects (font (size 1.0 1.0)))))
      )
    )"""


def lib_sym_power(name: str, net_name: str) -> str:
    """Generate a power symbol definition (GND, +3.3V, etc.)."""
    sym_name = name.split(':')[-1] if ':' in name else name
    if "GND" in name:
        drawing = """      (polyline (pts (xy 0 0) (xy 0 -1.27) (xy -1.27 -1.27) (xy 0 -2.54) (xy 1.27 -1.27) (xy 0 -1.27))
        (stroke (width 0) (type default)) (fill (type none)))"""
        pin_at = "(at 0 0 0)"
    else:
        drawing = """      (polyline (pts (xy -0.762 1.27) (xy 0.762 1.27))
        (stroke (width 0.254) (type default)) (fill (type none)))
      (polyline (pts (xy 0 0) (xy 0 1.27))
        (stroke (width 0) (type default)) (fill (type none)))"""
        pin_at = "(at 0 0 90)"

    return f"""    (symbol "{name}"
      (power) (pin_numbers hide) (pin_names hide) (in_bom no) (on_board yes)
      (property "Reference" "#PWR" (at 0 2.54 0)
        (effects (font (size 1.27 1.27)) hide))
      (property "Value" "{net_name}" (at 0 3.81 0)
        (effects (font (size 1.0 1.0))))
      (property "Footprint" "" (at 0 0 0)
        (effects (font (size 1.27 1.27)) hide))
      (symbol "{sym_name}_0_1"
{drawing}
      )
      (symbol "{sym_name}_1_1"
        (pin power_in line {pin_at} (length 0)
          (name "{net_name}" (effects (font (size 1.0 1.0))))
          (number "1" (effects (font (size 1.0 1.0)))))
      )
    )"""


def lib_sym_pwr_flag() -> str:
    """Generate PWR_FLAG symbol. Place on every power output net to avoid
    'power_pin_not_driven' ERC errors."""
    return """    (symbol "power:PWR_FLAG"
      (power) (pin_numbers hide) (pin_names hide) (in_bom no) (on_board yes)
      (property "Reference" "#FLG" (at 0 2.54 0)
        (effects (font (size 1.27 1.27)) hide))
      (property "Value" "PWR_FLAG" (at 0 3.81 0)
        (effects (font (size 1.0 1.0))))
      (property "Footprint" "" (at 0 0 0)
        (effects (font (size 1.27 1.27)) hide))
      (symbol "PWR_FLAG_0_1"
        (polyline (pts (xy 0 0) (xy 0 1.27) (xy -1.016 2.032) (xy 0 2.794) (xy 1.016 2.032) (xy 0 1.27))
          (stroke (width 0) (type default)) (fill (type none)))
      )
      (symbol "PWR_FLAG_1_1"
        (pin power_out line (at 0 0 90) (length 0)
          (name "pwr" (effects (font (size 1.0 1.0))))
          (number "1" (effects (font (size 1.0 1.0)))))
      )
    )"""


# =============================================================================
# Sub-symbol name fixer (post-processing)
# =============================================================================

def fix_subsymbol_names(content: str) -> str:
    """
    Fix sub-symbol names in lib_symbols section.

    KiCad REQUIRES that sub-symbols (those with _N_N suffix) do NOT include
    the library prefix. This is the most common cause of "Invalid symbol unit
    name prefix" errors when opening generated schematics.

    Examples of what this fixes:
        "Device:R_0_1"              → "R_0_1"
        "Device:C_Polarized_0_1"    → "C_Polarized_0_1"
        "CubeSat_SDR:AD9363ABCZ_1_1" → "AD9363ABCZ_1_1"
        "Connector:Barrel_Jack_0_1" → "Barrel_Jack_0_1"
    """
    def fix_match(m):
        full_name = m.group(1)
        suffix = m.group(2)
        if ':' in full_name:
            name = full_name.split(':', 1)[1]
            return f'(symbol "{name}{suffix}"'
        return m.group(0)

    return re.sub(r'\(symbol "([^"]+?)(_\d+_\d+)"', fix_match, content)


# =============================================================================
# Schematic builder
# =============================================================================

@dataclass
class PlacedComponent:
    """A component placed in the schematic."""
    lib_id: str
    ref: str
    value: str
    x: float
    y: float
    rotation: int
    footprint: str
    lcsc: str
    mirror_y: bool
    unit: int
    uuid: str


class SchematicBuilder:
    """
    Build a KiCad 8 schematic with guaranteed pin-label connectivity.

    All coordinates are automatically grid-snapped.
    Use connect_pin() for IC pins — it computes exact positions.
    Use place_2pin_vertical/horizontal for passive components.
    """

    def __init__(self, symbol_lib: SymbolLibrary = None, project_name: str = "project"):
        self.symbol_lib = symbol_lib
        self.project_name = project_name
        self.root_uuid = uid()
        self.components: list = []
        self.placed: dict = {}  # ref -> PlacedComponent
        self.wires: list = []
        self.labels: list = []
        self.no_connects: list = []
        self.text_notes: list = []
        self.pwr_sym_counter = 0
        self.flg_counter = 0
        self._lib_symbols_content = ""

    def set_symbol_library(self, lib: SymbolLibrary):
        """Set the symbol library for pin position lookups."""
        self.symbol_lib = lib

    def set_lib_symbols(self, content: str):
        """Set raw lib_symbols S-expression content."""
        self._lib_symbols_content = content

    def place(self, lib_id: str, ref: str, value: str, x: float, y: float,
              rotation: int = 0, footprint: str = "", lcsc: str = "",
              mirror_y: bool = False, unit: int = 1) -> PlacedComponent:
        """Place a component at grid-snapped coordinates."""
        x, y = snap(x), snap(y)
        u = uid()
        ms = "(mirror y)" if mirror_y else ""
        mirror = f" {ms}" if ms else ""

        self.components.append(f"""  (symbol (lib_id "{lib_id}") (at {x:.2f} {y:.2f} {rotation}){mirror}
    (uuid "{u}")
    (property "Reference" "{ref}" (at {x:.2f} {y - 3.81:.2f} 0)
      (effects (font (size 1.27 1.27))))
    (property "Value" "{value}" (at {x:.2f} {y + 3.81:.2f} 0)
      (effects (font (size 1.0 1.0))))
    (property "Footprint" "{footprint}" (at {x:.2f} {y + 5.08:.2f} 0)
      (effects (font (size 1.27 1.27)) hide))
    (property "LCSC" "{lcsc}" (at {x:.2f} {y + 6.35:.2f} 0)
      (effects (font (size 1.27 1.27)) hide))
    (instances
      (project "{self.project_name}"
        (path "/{self.root_uuid}" (reference "{ref}") (unit {unit}))
      )
    )
  )""")

        comp = PlacedComponent(
            lib_id=lib_id, ref=ref, value=value,
            x=x, y=y, rotation=rotation,
            footprint=footprint, lcsc=lcsc,
            mirror_y=mirror_y, unit=unit, uuid=u
        )
        self.placed[ref] = comp
        return comp

    def place_power(self, lib_id: str, value: str, x: float, y: float, rotation: int = 0):
        """Place a power symbol (GND, VCC, etc.)."""
        x, y = snap(x), snap(y)
        self.pwr_sym_counter += 1
        ref = f"#PWR{self.pwr_sym_counter:03d}"
        self.components.append(f"""  (symbol (lib_id "{lib_id}") (at {x:.2f} {y:.2f} {rotation})
    (uuid "{uid()}")
    (property "Reference" "{ref}" (at {x:.2f} {y + 2.54:.2f} 0)
      (effects (font (size 1.27 1.27)) hide))
    (property "Value" "{value}" (at {x:.2f} {y + 3.81:.2f} 0)
      (effects (font (size 0.8 0.8))))
    (property "Footprint" "" (at {x:.2f} {y:.2f} 0)
      (effects (font (size 1.27 1.27)) hide))
    (instances
      (project "{self.project_name}"
        (path "/{self.root_uuid}" (reference "{ref}") (unit 1))
      )
    )
  )""")

    def place_pwr_flag(self, x: float, y: float, net_name: str):
        """Place a PWR_FLAG on a power net. Essential for regulator outputs."""
        x, y = snap(x), snap(y)
        self.flg_counter += 1
        ref = f"#FLG{self.flg_counter:03d}"
        self.components.append(f"""  (symbol (lib_id "power:PWR_FLAG") (at {x:.2f} {y:.2f} 0)
    (uuid "{uid()}")
    (property "Reference" "{ref}" (at {x:.2f} {y + 2.54:.2f} 0)
      (effects (font (size 1.27 1.27)) hide))
    (property "Value" "PWR_FLAG" (at {x:.2f} {y + 3.81:.2f} 0)
      (effects (font (size 0.8 0.8))))
    (property "Footprint" "" (at {x:.2f} {y:.2f} 0)
      (effects (font (size 1.27 1.27)) hide))
    (instances
      (project "{self.project_name}"
        (path "/{self.root_uuid}" (reference "{ref}") (unit 1))
      )
    )
  )""")
        self.label(net_name, x, y)

    def connect_pin(self, ref: str, pin_name: str, net_label: str,
                    wire_dx: float = 0, wire_dy: float = 0,
                    label_angle: int = 0, by_number: bool = False):
        """
        THE key method. Connect a component's pin to a net label with exact
        computed coordinates and an optional wire stub.

        This eliminates dangling label and unconnected pin ERC errors.

        Args:
            ref: Component reference (e.g., "U1")
            pin_name: Pin name (or number if by_number=True)
            net_label: Net label text
            wire_dx, wire_dy: Wire extension from pin for routing room
            label_angle: Label rotation (0, 90, 180, 270)
            by_number: Look up pin by number instead of name
        """
        comp = self.placed.get(ref)
        if not comp:
            print(f"WARNING: Component {ref} not found", file=sys.stderr)
            return

        if not self.symbol_lib:
            print(f"WARNING: No symbol library set. Pass symbol_lib to constructor "
                  f"or call set_symbol_library() first.", file=sys.stderr)
            return

        sym_def = self.symbol_lib.get(comp.lib_id)
        if not sym_def:
            print(f"WARNING: Symbol {comp.lib_id} not in library", file=sys.stderr)
            return

        pin = (sym_def.get_pin_by_number(pin_name) if by_number
               else sym_def.get_pin(pin_name))
        if not pin:
            print(f"WARNING: Pin '{pin_name}' not found on {comp.lib_id}",
                  file=sys.stderr)
            return

        abs_x, abs_y = pin_abs(comp.x, comp.y, pin.x, pin.y,
                                comp.rotation, comp.mirror_y)
        end_x = snap(abs_x + wire_dx)
        end_y = snap(abs_y + wire_dy)

        if wire_dx != 0 or wire_dy != 0:
            self.wire(abs_x, abs_y, end_x, end_y)
            self.label(net_label, end_x, end_y, label_angle)
        else:
            self.label(net_label, abs_x, abs_y, label_angle)

    def connect_pin_noconnect(self, ref: str, pin_name: str, by_number: bool = False):
        """Place a no-connect flag on an unused pin."""
        comp = self.placed.get(ref)
        if not comp or not self.symbol_lib:
            return
        sym_def = self.symbol_lib.get(comp.lib_id)
        if not sym_def:
            return
        pin = (sym_def.get_pin_by_number(pin_name) if by_number
               else sym_def.get_pin(pin_name))
        if not pin:
            return
        abs_x, abs_y = pin_abs(comp.x, comp.y, pin.x, pin.y,
                                comp.rotation, comp.mirror_y)
        self.no_connect(abs_x, abs_y)

    # Alias for backward compatibility
    connect_pin_nc = connect_pin_noconnect

    def wire(self, x1: float, y1: float, x2: float, y2: float):
        """Draw a wire (auto-snapped). Skips zero-length wires."""
        x1, y1, x2, y2 = snap(x1), snap(y1), snap(x2), snap(y2)
        if x1 == x2 and y1 == y2:
            return
        self.wires.append(f"""  (wire (pts (xy {x1:.2f} {y1:.2f}) (xy {x2:.2f} {y2:.2f}))
    (stroke (width 0) (type default))
    (uuid "{uid()}")
  )""")

    # Short alias
    w = wire

    def label(self, name: str, x: float, y: float, angle: int = 0):
        """Place a net label (auto-snapped)."""
        x, y = snap(x), snap(y)
        self.labels.append(f"""  (label "{name}" (at {x:.2f} {y:.2f} {angle})
    (effects (font (size 1.27 1.27)) (justify left))
    (uuid "{uid()}")
  )""")

    def no_connect(self, x: float, y: float):
        """Place a no-connect flag (auto-snapped)."""
        x, y = snap(x), snap(y)
        self.no_connects.append(f"""  (no_connect (at {x:.2f} {y:.2f})
    (uuid "{uid()}")
  )""")

    # Short alias
    nc = no_connect

    def text_note(self, text: str, x: float, y: float, size: float = 2.54):
        """Add a text annotation."""
        self.text_notes.append(f"""  (text "{text}" (at {x:.2f} {y:.2f} 0)
    (effects (font (size {size} {size})) (justify left))
    (uuid "{uid()}")
  )""")

    def build(self, title: str = "Schematic", date: str = "2026-01-01",
              rev: str = "1.0", paper: str = "A1", comments: list = None) -> str:
        """Generate the complete .kicad_sch file.
        IMPORTANT: Always run fix_subsymbol_names() on the output!"""
        comment_lines = ""
        if comments:
            for i, c in enumerate(comments, 1):
                comment_lines += f'    (comment {i} "{c}")\n'

        # KiCad 7.0.x (Ubuntu packages) rejects generator_version / quoted generator.
        # Emit the 20230121 schematic dialect so kicad-cli can load and export.
        header = f"""(kicad_sch
  (version 20230121)
  (generator eeschema)
  (uuid "{self.root_uuid}")
  (paper "{paper}")
  (title_block
    (title "{title}")
    (date "{date}")
    (rev "{rev}")
{comment_lines}  )"""

        all_items = (self.components + self.wires + self.labels +
                     self.no_connects + self.text_notes)

        return f"""{header}

  (lib_symbols
{self._lib_symbols_content}
  )

{chr(10).join(all_items)}

  (sheet_instances
    (path "/"
      (page "1")
    )
  )
)"""


# =============================================================================
# Convenience helpers for 2-pin components
# =============================================================================

def place_2pin_vertical(builder: SchematicBuilder, lib_id: str, ref: str,
                        value: str, x: float, y: float,
                        top_net: str, bottom_net: str,
                        footprint: str = "", lcsc: str = "",
                        wire_ext: float = 3.81):
    """
    Place a 2-pin component vertically and wire both pins to net labels.

    Pin layout (rotation 0):
        Pin 1 at lib (0, 2.54) -> schematic TOP  -> connects to top_net
        Pin 2 at lib (0, -2.54) -> schematic BOTTOM -> connects to bottom_net

    Wire stubs extend wire_ext mm from each pin.
    """
    x, y = snap(x), snap(y)
    builder.place(lib_id, ref, value, x, y, footprint=footprint, lcsc=lcsc)
    p1y = snap(y - 2.54)  # Pin 1 in schematic (Y negated)
    p2y = snap(y + 2.54)  # Pin 2 in schematic
    builder.wire(x, p1y, x, snap(p1y - wire_ext))
    builder.label(top_net, x, snap(p1y - wire_ext))
    builder.wire(x, p2y, x, snap(p2y + wire_ext))
    builder.label(bottom_net, x, snap(p2y + wire_ext))


def place_2pin_horizontal(builder: SchematicBuilder, lib_id: str, ref: str,
                          value: str, x: float, y: float,
                          left_net: str, right_net: str,
                          footprint: str = "", lcsc: str = "",
                          wire_ext: float = 3.81):
    """
    Place a 2-pin component horizontally (rotation=90) and wire both pins.

    Pin layout (rotation 90):
        Pin 1 at lib (0, 2.54) -> schematic RIGHT -> connects to right_net
        Pin 2 at lib (0, -2.54) -> schematic LEFT -> connects to left_net
    """
    x, y = snap(x), snap(y)
    builder.place(lib_id, ref, value, x, y, rotation=90,
                  footprint=footprint, lcsc=lcsc)
    p1x = snap(x + 2.54)  # Pin 1 in schematic (rotation 90)
    p2x = snap(x - 2.54)  # Pin 2
    builder.wire(p1x, y, snap(p1x + wire_ext), y)
    builder.label(right_net, snap(p1x + wire_ext), y)
    builder.wire(p2x, y, snap(p2x - wire_ext), y)
    builder.label(left_net, snap(p2x - wire_ext), y)


# =============================================================================
# ERC validation
# =============================================================================

def run_erc(schematic_path: str, output_path: str = None,
            kicad_cli: str = "kicad-cli",
            env_vars: dict = None) -> dict:
    """
    Run KiCad ERC check via kicad-cli and return structured results.

    Args:
        schematic_path: Path to the .kicad_sch file
        output_path: Where to write JSON results (default: alongside schematic)
        kicad_cli: Path to kicad-cli executable
        env_vars: Extra environment variables (e.g., KICAD9_SYMBOL_DIR,
                  KICAD9_FOOTPRINT_DIR for macOS KiCad 9)

    Returns:
        dict with: success (bool), errors (int), warnings (int),
                   error_types (dict), details (list)

    Note: JSON output uses sheets[].violations[] format, not top-level violations.
          This function handles both formats automatically.
    """
    import os as _os

    if output_path is None:
        output_path = str(Path(schematic_path).with_suffix('.erc.json'))

    # Build environment with optional extra vars (needed for macOS KiCad 9)
    run_env = _os.environ.copy()
    if env_vars:
        run_env.update(env_vars)

    try:
        result = subprocess.run(
            [kicad_cli, "sch", "erc",
             "--output", output_path, "--format", "json",
             "--severity-all", schematic_path],
            capture_output=True, text=True, timeout=60,
            env=run_env
        )
    except FileNotFoundError:
        # Try to auto-discover kicad-cli
        found = find_kicad_cli()
        if found:
            print(f"WARNING: kicad-cli not on PATH but found at: {found}",
                  file=sys.stderr)
            suggest_kicad_cli_symlink()
            try:
                result = subprocess.run(
                    [found, "sch", "erc",
                     "--output", output_path, "--format", "json",
                     "--severity-all", schematic_path],
                    capture_output=True, text=True, timeout=60,
                    env=run_env
                )
            except Exception as e:
                return {"success": False, "errors": -1, "warnings": -1,
                        "total": -1, "details": [],
                        "raw": f"kicad-cli found at {found} but failed: {e}"}
        else:
            suggest_kicad_cli_symlink()
            return {"success": False, "errors": -1, "warnings": -1,
                    "total": -1, "details": [], "raw": "kicad-cli not found"}
    except subprocess.TimeoutExpired:
        return {"success": False, "errors": -1, "warnings": -1,
                "total": -1, "details": [], "raw": "timeout"}

    try:
        with open(output_path) as f:
            report = json.load(f)
    except (json.JSONDecodeError, FileNotFoundError):
        return _parse_text_erc(result.stdout + result.stderr)

    # Handle both KiCad 8 (top-level violations) and KiCad 9 (sheets[].violations[])
    all_violations = []
    if "violations" in report:
        all_violations = report["violations"]
    elif "sheets" in report:
        for sheet in report["sheets"]:
            all_violations.extend(sheet.get("violations", []))

    errors = [v for v in all_violations if v.get("severity") == "error"]
    warnings = [v for v in all_violations if v.get("severity") == "warning"]

    return {
        "success": len(errors) == 0,
        "errors": len(errors), "warnings": len(warnings),
        "total": len(errors) + len(warnings),
        "details": all_violations,
        "error_types": _categorize(errors),
        "warning_types": _categorize(warnings),
    }


def validate_and_fix_loop(schematic_path: str, fix_callback,
                           max_iterations: int = 5,
                           kicad_cli: str = "kicad-cli") -> dict:
    """
    Automated generate -> validate -> fix loop.

    Args:
        schematic_path: Path to the schematic file
        fix_callback: Function(erc_result, iteration) -> bool
                      Returns True if fixes were applied, False to stop
        max_iterations: Maximum fix attempts
        kicad_cli: Path to kicad-cli

    Returns:
        Final ERC result dict
    """
    for i in range(max_iterations):
        print(f"\n=== ERC Validation Iteration {i+1}/{max_iterations} ===")
        result = run_erc(schematic_path, kicad_cli=kicad_cli)
        print(f"Errors: {result['errors']}, Warnings: {result['warnings']}")

        if result["errors"] == 0:
            print("No ERC errors!")
            return result

        if not fix_callback(result, i):
            print("Fix callback returned False, stopping.")
            return result

    print(f"Reached max iterations ({max_iterations})")
    return result


def _categorize(violations):
    cats = {}
    for v in violations:
        cats[v.get("type", "unknown")] = cats.get(v.get("type", "unknown"), 0) + 1
    return cats


def _parse_text_erc(text):
    errors = len(re.findall(r';\s*error', text))
    warnings = len(re.findall(r';\s*warning', text))
    return {"success": errors == 0, "errors": errors, "warnings": warnings,
            "total": errors + warnings, "details": [], "raw": text}


# =============================================================================
# kicad-cli discovery and symlink helper
# =============================================================================

def find_kicad_cli() -> Optional[str]:
    """
    Locate kicad-cli on the system. Returns the path if found, None otherwise.
    Checks PATH first, then common installation directories per OS.
    """
    import shutil
    import platform

    found = shutil.which("kicad-cli")
    if found:
        return found

    system = platform.system()

    candidates = []
    if system == "Darwin":
        candidates = [
            "/Applications/KiCad/KiCad.app/Contents/MacOS/kicad-cli",
            "/Applications/KiCad 9.0/KiCad.app/Contents/MacOS/kicad-cli",
            "/Applications/KiCad 8.0/KiCad.app/Contents/MacOS/kicad-cli",
            Path.home() / "Applications/KiCad/KiCad.app/Contents/MacOS/kicad-cli",
        ]
    elif system == "Linux":
        candidates = [
            "/usr/bin/kicad-cli",
            "/usr/local/bin/kicad-cli",
            "/snap/kicad/current/bin/kicad-cli",
            Path.home() / ".local/bin/kicad-cli",
        ]
    elif system == "Windows":
        candidates = [
            Path(r"C:\Program Files\KiCad\9.0\bin\kicad-cli.exe"),
            Path(r"C:\Program Files\KiCad\8.0\bin\kicad-cli.exe"),
            Path(r"C:\Program Files\KiCad\bin\kicad-cli.exe"),
            Path(r"C:\Program Files (x86)\KiCad\8.0\bin\kicad-cli.exe"),
        ]

    for candidate in candidates:
        if Path(candidate).is_file():
            return str(candidate)

    return None


def suggest_kicad_cli_symlink() -> Optional[str]:
    """
    Find kicad-cli and print instructions to make it available on PATH.
    Returns the found path, or None if not installed.
    """
    import platform

    found = find_kicad_cli()
    if not found:
        system = platform.system()
        urls = {
            "Darwin": "https://www.kicad.org/download/macos/",
            "Linux": "https://www.kicad.org/download/linux/",
            "Windows": "https://www.kicad.org/download/windows/",
        }
        url = urls.get(system, "https://www.kicad.org/download/")
        print(f"kicad-cli not found. Install KiCad 8 from: {url}", file=sys.stderr)
        return None

    import shutil
    if shutil.which("kicad-cli"):
        return found

    system = platform.system()
    if system in ("Darwin", "Linux"):
        print(f"Found kicad-cli at: {found}", file=sys.stderr)
        print(f"To add to PATH, run:", file=sys.stderr)
        print(f"  sudo ln -sf '{found}' /usr/local/bin/kicad-cli", file=sys.stderr)
    elif system == "Windows":
        bin_dir = str(Path(found).parent)
        print(f"Found kicad-cli at: {found}", file=sys.stderr)
        print(f"To add to PATH, run in PowerShell (as admin):", file=sys.stderr)
        print(f'  [Environment]::SetEnvironmentVariable("PATH", $env:PATH + ";{bin_dir}", "User")',
              file=sys.stderr)

    return found


# =============================================================================
# ERC fixing utilities — for modifying existing schematics
# =============================================================================

def find_block(content: str, start_pos: int) -> tuple:
    """
    Find a balanced parenthesized block starting at start_pos.

    Handles quoted strings correctly (parentheses inside quotes are ignored).

    Args:
        content: The full file content
        start_pos: Position of the opening '('

    Returns:
        (block_text, end_pos) where end_pos is the position after the closing ')'

    Raises:
        ValueError: If no '(' at start_pos or parentheses are unbalanced

    Example:
        >>> content = '(symbol "Device:R" (pin passive line))'
        >>> text, end = find_block(content, 0)
        >>> text
        '(symbol "Device:R" (pin passive line))'
    """
    if content[start_pos] != '(':
        raise ValueError(f"Expected '(' at position {start_pos}, got '{content[start_pos]}'")
    depth = 0
    i = start_pos
    in_string = False
    while i < len(content):
        c = content[i]
        if c == '"' and (i == 0 or content[i-1] != '\\'):
            in_string = not in_string
        elif not in_string:
            if c == '(':
                depth += 1
            elif c == ')':
                depth -= 1
                if depth == 0:
                    return content[start_pos:i+1], i + 1
        i += 1
    raise ValueError(f"Unbalanced parentheses starting at {start_pos}")


def remove_block_with_whitespace(content: str, block_start: int, block_end: int) -> str:
    """
    Remove a block and its surrounding whitespace/newlines cleanly.

    Looks backwards for preceding whitespace/tabs and a newline,
    and forward for trailing whitespace and a newline. Removes all of it
    so no blank lines are left behind.

    Args:
        content: The full file content
        block_start: Start position of the block (the opening paren)
        block_end: End position of the block (after the closing paren)

    Returns:
        Modified content with the block and surrounding whitespace removed
    """
    start = block_start
    while start > 0 and content[start-1] in ' \t':
        start -= 1
    if start > 0 and content[start-1] == '\n':
        start -= 1
    end = block_end
    while end < len(content) and content[end] in ' \t':
        end += 1
    if end < len(content) and content[end] == '\n':
        end += 1
    return content[:start] + content[end:]


def extract_embedded_symbol(content: str, symbol_name: str) -> Optional[str]:
    """
    Extract an embedded lib_symbol block by its full name.

    Searches the lib_symbols section of a .kicad_sch file for a symbol
    with the given name (e.g., 'Connector:Conn_01x04' or 'CubeSat_SDR:AMS1117')
    and returns the complete s-expression block.

    Args:
        content: The full .kicad_sch file content
        symbol_name: Full prefixed symbol name (e.g., 'CubeSat_SDR:AMS1117')

    Returns:
        The symbol block text, or None if not found
    """
    pattern = f'(symbol "{symbol_name}"'
    pos = content.find(pattern)
    if pos == -1:
        return None
    block_text, _ = find_block(content, pos)
    return block_text


def convert_embedded_to_library(block_text: str, old_prefix: str, new_name: str) -> str:
    """
    Convert an embedded lib_symbol to standalone library format.

    In embedded format: top-level is (symbol "Prefix:Name" ...)
    In library format: top-level is (symbol "Name" ...)
    Sub-symbols (Name_0_1, Name_1_1) remain unchanged in both formats.

    Args:
        block_text: The extracted symbol block
        old_prefix: The library prefix to remove (e.g., "Connector", "CubeSat_SDR")
        new_name: The symbol name without prefix (e.g., "Conn_01x04")

    Returns:
        The converted block suitable for a .kicad_sym library file
    """
    return block_text.replace(
        f'(symbol "{old_prefix}:{new_name}"',
        f'(symbol "{new_name}"',
        1
    )


def find_by_uuid(content: str, uuid: str) -> Optional[int]:
    """
    Find the position of a UUID string in the content.

    Args:
        content: The full file content
        uuid: The UUID to search for

    Returns:
        Position of the UUID marker, or None if not found
    """
    marker = f'(uuid "{uuid}")'
    pos = content.find(marker)
    return pos if pos != -1 else None


def remove_by_uuid(content: str, uuid: str, element_type: str) -> str:
    """
    Remove an element (symbol, wire, no_connect, label) by its UUID.

    Searches backwards from the UUID to find the containing block of the
    specified type, then removes it with surrounding whitespace.

    Args:
        content: The full file content
        uuid: The UUID of the element to remove
        element_type: The s-expression type ('symbol', 'wire', 'no_connect', 'label')

    Returns:
        Modified content with the element removed

    Raises:
        ValueError: If UUID not found or parent block not found

    Example:
        >>> content = remove_by_uuid(content, "ac2d9711-...", "symbol")
    """
    marker = f'(uuid "{uuid}")'
    pos = content.find(marker)
    if pos == -1:
        raise ValueError(f"UUID '{uuid}' not found in content")

    # Search backwards for the containing element
    search_term = f'({element_type}'
    block_start = content.rfind(search_term, 0, pos)
    if block_start == -1:
        raise ValueError(f"Could not find parent ({element_type} block for UUID '{uuid}'")

    block_text, block_end = find_block(content, block_start)
    if uuid not in block_text:
        raise ValueError(f"Found ({element_type} block but UUID '{uuid}' not inside it")

    return remove_block_with_whitespace(content, block_start, block_end)


def replace_lib_id(content: str, old_id: str, new_id: str) -> tuple:
    """
    Replace a lib_id across all symbol instances and embedded lib_symbols.

    Updates both:
    - (lib_id "old_id") in placed symbol instances
    - (symbol "old_id" ...) in the embedded lib_symbols section

    Args:
        content: The full .kicad_sch file content
        old_id: The old lib_id (e.g., "Connector:Conn_01x04")
        new_id: The new lib_id (e.g., "CubeSat_SDR:Conn_01x04")

    Returns:
        (modified_content, count) where count is total replacements made

    Example:
        >>> content, n = replace_lib_id(content, "Connector:SMA", "CubeSat_SDR:SMA")
        >>> print(f"Replaced {n} occurrences")
    """
    count = 0

    # Replace in placed symbol instances
    old_str = f'(lib_id "{old_id}")'
    new_str = f'(lib_id "{new_id}")'
    c = content.count(old_str)
    content = content.replace(old_str, new_str)
    count += c

    # Replace in embedded lib_symbol key
    old_sym = f'(symbol "{old_id}"'
    new_sym = f'(symbol "{new_id}"'
    if old_sym in content:
        content = content.replace(old_sym, new_sym)
        count += 1

    return content, count


def replace_footprint(content: str, old_fp: str, new_fp: str) -> tuple:
    """
    Replace a footprint reference across all symbol instances.

    Args:
        content: The full .kicad_sch file content
        old_fp: The old footprint (e.g., "Button_Switch_SMD:SW_Push_1P1T_NO_6x3.5mm")
        new_fp: The new footprint (e.g., "Button_Switch_SMD:SW_Push_1P1T_NO_CK_PTS125Sx43SMTR")

    Returns:
        (modified_content, count) where count is number of replacements

    Example:
        >>> content, n = replace_footprint(content,
        ...     "Connector_Coaxial:SMA_Amphenol_901-143_Vertical",
        ...     "Connector_Coaxial:SMA_Amphenol_901-144_Vertical")
    """
    old_str = f'"Footprint" "{old_fp}"'
    new_str = f'"Footprint" "{new_fp}"'
    count = content.count(old_str)
    content = content.replace(old_str, new_str)
    return content, count


def fix_annotation_suffixes(content: str) -> tuple:
    """
    Ensure all reference designators end with a digit (KiCad 9 requirement).

    KiCad 9's GUI requires all references to end with a number. References
    like 'C_RX1B_N' or 'J_PWR' cause "Item not annotated" errors. This
    function appends '1' to any reference that doesn't end with a digit.

    Handles both:
    - (property "Reference" "C_RX1B_N" ...) in symbol properties
    - (reference "C_RX1B_N") in instance paths

    Args:
        content: The full .kicad_sch file content

    Returns:
        (modified_content, fixed_refs) where fixed_refs is list of refs that were fixed

    Example:
        >>> content, refs = fix_annotation_suffixes(content)
        >>> print(f"Fixed {len(refs)} references: {refs}")
    """
    # Find all instance references (excluding hidden #FLG, #PWR)
    refs = re.findall(r'\(reference "([^"]+)"\)', content)
    visible_refs = [r for r in refs if not r.startswith('#')]
    no_digit = sorted(set(r for r in visible_refs if r and not r[-1].isdigit()))

    for ref in no_digit:
        new_ref = ref + "1"
        # Replace in property "Reference"
        old_prop = f'"Reference" "{ref}"'
        new_prop = f'"Reference" "{new_ref}"'
        content = content.replace(old_prop, new_prop)

        # Replace in instance (reference ...)
        old_inst = f'(reference "{ref}")'
        new_inst = f'(reference "{new_ref}")'
        content = content.replace(old_inst, new_inst)

    return content, no_digit


def create_pwr_flag_block(x: float, y: float, ref_num: int,
                          project_name: str, root_uuid: str) -> str:
    """
    Generate a PWR_FLAG symbol s-expression block for insertion into a schematic.

    Use this to fix 'power_pin_not_driven' ERC errors. Place the PWR_FLAG
    on a wire connected to the power input pin.

    Args:
        x, y: Position in schematic coordinates (should be on a wire)
        ref_num: Reference number (e.g., 7 for #FLG07)
        project_name: Project name for the instances section
        root_uuid: Root sheet UUID for the instances path

    Returns:
        Complete s-expression block ready to insert into the schematic

    Example:
        >>> block = create_pwr_flag_block(34.29, 77.47, 7, "cubesat_sdr",
        ...     "5fb33c66-7637-43ae-9eef-34b4f23f6cfb")
    """
    sym_uuid = uid()
    pin_uuid = uid()
    ref = f"#FLG{ref_num:02d}"

    return f"""\t(symbol
\t\t(lib_id "power:PWR_FLAG")
\t\t(at {x} {y} 0)
\t\t(unit 1)
\t\t(exclude_from_sim no)
\t\t(in_bom yes)
\t\t(on_board yes)
\t\t(dnp no)
\t\t(uuid "{sym_uuid}")
\t\t(property "Reference" "{ref}"
\t\t\t(at {x} {y - 2.54} 0)
\t\t\t(effects
\t\t\t\t(font
\t\t\t\t\t(size 1.27 1.27)
\t\t\t\t)
\t\t\t\t(hide yes)
\t\t\t)
\t\t)
\t\t(property "Value" "PWR_FLAG"
\t\t\t(at {x} {y - 3.81} 0)
\t\t\t(effects
\t\t\t\t(font
\t\t\t\t\t(size 0.8 0.8)
\t\t\t\t)
\t\t\t)
\t\t)
\t\t(property "Footprint" ""
\t\t\t(at {x} {y} 0)
\t\t\t(effects
\t\t\t\t(font
\t\t\t\t\t(size 1.27 1.27)
\t\t\t\t)
\t\t\t\t(hide yes)
\t\t\t)
\t\t)
\t\t(property "Datasheet" ""
\t\t\t(at {x} {y} 0)
\t\t\t(effects
\t\t\t\t(font
\t\t\t\t\t(size 1.27 1.27)
\t\t\t\t)
\t\t\t)
\t\t)
\t\t(property "Description" ""
\t\t\t(at {x} {y} 0)
\t\t\t(effects
\t\t\t\t(font
\t\t\t\t\t(size 1.27 1.27)
\t\t\t\t)
\t\t\t)
\t\t)
\t\t(pin "1"
\t\t\t(uuid "{pin_uuid}")
\t\t)
\t\t(instances
\t\t\t(project "{project_name}"
\t\t\t\t(path "/{root_uuid}"
\t\t\t\t\t(reference "{ref}")
\t\t\t\t\t(unit 1)
\t\t\t\t)
\t\t\t)
\t\t)
\t)"""


def suppress_erc_warning(pro_path: str, rule_name: str) -> None:
    """
    Suppress an ERC warning type in the .kicad_pro file.

    Only use for warnings that are known-safe (e.g., lib_symbol_mismatch
    during KiCad 8→9 migration). Never suppress errors.

    Args:
        pro_path: Path to the .kicad_pro file
        rule_name: The rule to suppress (e.g., 'lib_symbol_mismatch')
    """
    with open(pro_path) as f:
        pro = json.load(f)

    if 'erc' not in pro:
        pro['erc'] = {}
    if 'rule_severities' not in pro['erc']:
        pro['erc']['rule_severities'] = {}

    pro['erc']['rule_severities'][rule_name] = 'ignore'

    with open(pro_path, 'w') as f:
        json.dump(pro, f, indent=2)
        f.write('\n')


if __name__ == "__main__":
    print("KiCad Schematic Helper Library v3")
    print(f"Grid: {GRID} mm")
    print()

    # Test coordinate utilities
    print("=== Coordinate Utilities ===")
    print(f"snap(42.5) = {snap(42.5)}")
    print(f"pin_abs(320, 200, -17.78, 25.40, rotation=0) = "
          f"{pin_abs(320, 200, -17.78, 25.40, rotation=0)}")
    print(f"pin_abs(320, 200, 0, 2.54, rotation=90) = "
          f"{pin_abs(320, 200, 0, 2.54, rotation=90)}")
    print()

    # Test ERC fixing utilities
    print("=== ERC Fixing Utilities ===")
    test_content = '(symbol (lib_id "test") (at 0 0 0) (uuid "abc-123"))'
    block, end = find_block(test_content, 0)
    print(f"find_block: found block of {len(block)} chars, end at {end}")

    test_sch = 'before\n\t(wire (pts (xy 0 0) (xy 1 1))\n\t\t(uuid "wire-1")\n\t)\nafter'
    cleaned = remove_block_with_whitespace(test_sch, 8, test_sch.index(')') + 1)
    print(f"remove_block_with_whitespace: '{test_sch[:20]}...' -> '{cleaned[:20]}...'")

    # Test annotation suffix fixing
    test_refs = '(reference "C_RX1B_N")(reference "R1")(reference "J_PWR")'
    fixed, refs = fix_annotation_suffixes(test_refs)
    print(f"fix_annotation_suffixes: fixed {len(refs)} refs: {refs}")
    print()

    # Check kicad-cli
    print("=== kicad-cli ===")
    cli_path = find_kicad_cli()
    if cli_path:
        print(f"kicad-cli found: {cli_path}")
    else:
        suggest_kicad_cli_symlink()
