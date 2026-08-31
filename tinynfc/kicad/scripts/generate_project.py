#!/usr/bin/env python3
"""Generate the TinyNFC KiCad 7 schematic + PCB from the design spec.

Creates a batteryless NFC-harvested ATtiny816 + piezo design:
  NTAG I2C Plus (NT3H2111) harvests RF -> delayed P-FET bulk cap -> MCU PWM piezo.

Run from anywhere:
  python3 tinynfc/kicad/scripts/generate_project.py
"""

from __future__ import annotations

import json
import math
import uuid
from pathlib import Path

import pcbnew

ROOT = Path(__file__).resolve().parents[1]
LIB_DIR = ROOT / "libraries"
PRETTY = LIB_DIR / "tinynfc.pretty"
SYM = LIB_DIR / "tinynfc.kicad_sym"

# Postage-stamp disc: as small as the 9 mm piezo + spiral inductance allow.
# Round outline + circular spiral usually couple better to phone NFC coils.
BOARD_DIA_MM = 28.0
ANT_OUTER_DIA = 24.0
ANT_TURNS = 6
ANT_TRACE = 0.35
ANT_GAP = 0.28
ANT_PTS_PER_TURN = 64
# US quarter for scale drawings (documentation layer only — not fab copper).
US_QUARTER_DIA_MM = 24.26
BOARD_THICKNESS_MM = 1.6
PIEZO_HEIGHT_MM = 1.8

# Back-compat alias used in a few placement helpers.
BOARD_MM = BOARD_DIA_MM


def uid() -> str:
    return str(uuid.uuid4())


def mm(x: float) -> int:
    return int(pcbnew.FromMM(float(x)))


# ---------------------------------------------------------------------------
# Custom symbol library
# ---------------------------------------------------------------------------

NT3H_SYMBOL = r'''
  (symbol "NT3H2111W0FHKH" (in_bom yes) (on_board yes)
    (property "Reference" "U" (at 0 10.16 0)
      (effects (font (size 1.27 1.27)))
    )
    (property "Value" "NT3H2111W0FHKH" (at 0 -10.16 0)
      (effects (font (size 1.27 1.27)))
    )
    (property "Footprint" "tinynfc:NXP_SOT902-3_XQFN8" (at 0 0 0)
      (effects (font (size 1.27 1.27)) hide)
    )
    (property "Datasheet" "https://www.nxp.com/docs/en/data-sheet/NT3H2111_2211.pdf" (at 0 0 0)
      (effects (font (size 1.27 1.27)) hide)
    )
    (property "ki_keywords" "NFC NTAG energy harvest RFID" (at 0 0 0)
      (effects (font (size 1.27 1.27)) hide)
    )
    (property "ki_description" "NTAG I2C plus, energy harvesting, XQFN8 SOT902-3" (at 0 0 0)
      (effects (font (size 1.27 1.27)) hide)
    )
    (property "ki_fp_filters" "NXP_SOT902*" (at 0 0 0)
      (effects (font (size 1.27 1.27)) hide)
    )
    (symbol "NT3H2111W0FHKH_0_1"
      (rectangle (start -7.62 7.62) (end 7.62 -7.62)
        (stroke (width 0.254) (type default))
        (fill (type background))
      )
    )
    (symbol "NT3H2111W0FHKH_1_1"
      (pin passive line (at -10.16 5.08 0) (length 2.54)
        (name "LA" (effects (font (size 1.27 1.27))))
        (number "1" (effects (font (size 1.27 1.27))))
      )
      (pin power_in line (at 0 -10.16 90) (length 2.54)
        (name "VSS" (effects (font (size 1.27 1.27))))
        (number "2" (effects (font (size 1.27 1.27))))
      )
      (pin input line (at -10.16 0 0) (length 2.54)
        (name "SCL" (effects (font (size 1.27 1.27))))
        (number "3" (effects (font (size 1.27 1.27))))
      )
      (pin open_collector line (at -10.16 -5.08 0) (length 2.54)
        (name "FD" (effects (font (size 1.27 1.27))))
        (number "4" (effects (font (size 1.27 1.27))))
      )
      (pin bidirectional line (at 10.16 -5.08 180) (length 2.54)
        (name "SDA" (effects (font (size 1.27 1.27))))
        (number "5" (effects (font (size 1.27 1.27))))
      )
      (pin power_in line (at 0 10.16 270) (length 2.54)
        (name "VCC" (effects (font (size 1.27 1.27))))
        (number "6" (effects (font (size 1.27 1.27))))
      )
      (pin power_out line (at 10.16 5.08 180) (length 2.54)
        (name "VOUT" (effects (font (size 1.27 1.27))))
        (number "7" (effects (font (size 1.27 1.27))))
      )
      (pin passive line (at 10.16 0 180) (length 2.54)
        (name "LB" (effects (font (size 1.27 1.27))))
        (number "8" (effects (font (size 1.27 1.27))))
      )
    )
  )
'''


def extract_system_symbol(lib_path: Path, name: str) -> str:
    """Return one top-level symbol S-expr from a KiCad .kicad_sym file."""
    import re

    lines = lib_path.read_text().splitlines()
    start = None
    for i, line in enumerate(lines):
        if line.startswith(f'  (symbol "{name}"'):
            start = i
            break
    if start is None:
        raise RuntimeError(f"symbol {name} not found in {lib_path}")
    # Unit/body variants look like Name_0_1 / Name_1_1. Stop at the next real symbol.
    unit_re = re.compile(rf'^  \(symbol "{re.escape(name)}_\d+_\d+"')
    end = None
    for j in range(start + 1, len(lines)):
        if lines[j].startswith('  (symbol "'):
            if unit_re.match(lines[j]):
                continue
            end = j
            break
    if end is None:
        end = len(lines) - 1  # before final )
    return "\n".join(lines[start:end])


def write_symbol_library() -> None:
    LIB_DIR.mkdir(parents=True, exist_ok=True)
    mcu = Path("/tmp/attiny_sym.txt").read_text().rstrip()
    # Prefer the footprint that ships with KiCad for this MCU family.
    mcu = mcu.replace(
        'Package_DFN_QFN:VQFN-20-1EP_3x3mm_P0.4mm_EP1.7x1.7mm',
        'Package_DFN_QFN:VQFN-20-1EP_3x3mm_P0.4mm_EP1.7x1.7mm',
    )
    body = (
        '(kicad_symbol_lib (version 20220914) (generator "tinynfc-generate")\n'
        + NT3H_SYMBOL
        + "\n"
        + mcu
        + "\n)\n"
    )
    SYM.write_text(body)


def write_xqfn8_footprint() -> None:
    """NXP SOT902-3 / XQFN8 1.6x1.6 mm (approx. recommended land pattern)."""
    PRETTY.mkdir(parents=True, exist_ok=True)
    # Nominal land pattern from SOT902-3 style: 0.5 mm pitch, corner pads.
    # Pin 1 at top-left (LA), CCW: 1 LA, 2 VSS, 3 SCL, 4 FD, 5 SDA, 6 VCC, 7 VOUT, 8 LB
    # Looking from top: left side 1,2,3,4 top->bottom; right side 8,7,6,5 top->bottom.
    pitch = 0.50
    pad_w, pad_h = 0.30, 0.45
    x = 0.80  # pad center from package center
    ys = [1.5 * pitch / 2, 0.5 * pitch / 2, -0.5 * pitch / 2, -1.5 * pitch / 2]
    # left: pins 1..4 top to bottom; right: 8,7,6,5 top to bottom
    left = [(1, -x, ys[0]), (2, -x, ys[1]), (3, -x, ys[2]), (4, -x, ys[3])]
    right = [(8, x, ys[0]), (7, x, ys[1]), (6, x, ys[2]), (5, x, ys[3])]
    pads = left + right
    lines = [
        '(footprint "NXP_SOT902-3_XQFN8" (version 20221018) (generator "tinynfc")',
        '  (layer "F.Cu")',
        '  (descr "NXP SOT902-3 XQFN8 1.6x1.6mm for NT3H2111")',
        '  (tags "XQFN8 SOT902-3 NTAG")',
        "  (attr smd)",
        '  (fp_text reference "REF**" (at 0 -2.2) (layer "F.SilkS")',
        "    (effects (font (size 0.8 0.8) (thickness 0.12))))",
        '  (fp_text value "NXP_SOT902-3_XQFN8" (at 0 2.2) (layer "F.Fab")',
        "    (effects (font (size 0.8 0.8) (thickness 0.12))))",
        '  (fp_rect (start -0.8 -0.8) (end 0.8 0.8) (layer "F.Fab")',
        "    (stroke (width 0.1) (type solid)) (fill none))",
        '  (fp_rect (start -1.15 -1.15) (end 1.15 1.15) (layer "F.CrtYd")',
        "    (stroke (width 0.05) (type solid)) (fill none))",
        '  (fp_line (start -0.8 -0.55) (end -0.8 -0.8) (layer "F.SilkS") (stroke (width 0.12) (type solid)))',
        '  (fp_line (start -0.8 -0.8) (end -0.55 -0.8) (layer "F.SilkS") (stroke (width 0.12) (type solid)))',
        '  (fp_circle (center -1.05 -1.05) (end -0.95 -1.05) (layer "F.SilkS") (stroke (width 0.12) (type solid)) (fill solid))',
    ]
    for num, px, py in pads:
        lines.append(
            f'  (pad "{num}" smd rect (at {px:.3f} {py:.3f}) '
            f'(size {pad_w} {pad_h}) (layers "F.Cu" "F.Paste" "F.Mask"))'
        )
    lines.append(")\n")
    (PRETTY / "NXP_SOT902-3_XQFN8.kicad_mod").write_text("\n".join(lines))


def circular_spiral_points(
    outer_dia: float,
    turns: int,
    width: float,
    gap: float,
    pts_per_turn: int = ANT_PTS_PER_TURN,
) -> list[tuple[float, float]]:
    """Archimedean spiral centered at origin, outer diameter `outer_dia` mm."""
    pitch = width + gap
    r_max = outer_dia / 2
    total_theta = turns * 2 * math.pi
    n = max(8, int(turns * pts_per_turn))
    pts: list[tuple[float, float]] = []
    for i in range(n + 1):
        theta = total_theta * i / n
        r = r_max - pitch * theta / (2 * math.pi)
        if r < width + 0.5:
            break
        pts.append((r * math.cos(theta), r * math.sin(theta)))
    return pts


def write_antenna_footprint() -> None:
    """PCB circular spiral ~2.75 µH class; feeds on the inner rim (not under the piezo)."""
    pts = circular_spiral_points(ANT_OUTER_DIA, ANT_TURNS, ANT_TRACE, ANT_GAP)
    # Keep feeds on the west side of the inner turn so the 9 mm piezo can sit
    # at the geometric center without landing on antenna pads.
    feed_a = pts[-1]
    # Second feed one pitch inward along the same radial line.
    r_a = math.hypot(feed_a[0], feed_a[1])
    r_b = max(ANT_TRACE, r_a - (ANT_TRACE + ANT_GAP))
    scale = r_b / r_a if r_a else 0.0
    feed_b = (feed_a[0] * scale, feed_a[1] * scale)
    fab_y = ANT_OUTER_DIA / 2 + 1.2
    half = ANT_OUTER_DIA / 2 + 0.5
    lines = [
        '(footprint "PCB_Antenna_RoundSpiral" (version 20221018) (generator "tinynfc")',
        '  (layer "F.Cu")',
        '  (descr "Circular spiral NFC antenna ~2.75uH target; feed pads 1=LA 2=LB")',
        '  (tags "NFC antenna spiral 13.56MHz round postage-stamp")',
        "  (attr smd)",
        # Refs stay off F.SilkS so they never sit on spiral copper.
        f'  (fp_text reference "L1" (at 0 {fab_y:.2f}) (layer "F.Fab")',
        "    (effects (font (size 0.7 0.7) (thickness 0.1))))",
        f'  (fp_text value "PCB_Antenna_RoundSpiral" (at 0 {-fab_y:.2f}) (layer "F.Fab")',
        "    (effects (font (size 0.7 0.7) (thickness 0.1))))",
        f'  (fp_circle (center 0 0) (end {half:.2f} 0) (layer "F.CrtYd")'
        " (stroke (width 0.05) (type solid)) (fill none))",
    ]
    for a, b in zip(pts, pts[1:]):
        lines.append(
            f'  (fp_line (start {a[0]:.3f} {a[1]:.3f}) (end {b[0]:.3f} {b[1]:.3f}) '
            f'(layer "F.Cu") (stroke (width {ANT_TRACE}) (type solid)))'
        )
    lines.append(
        f'  (pad "1" smd rect (at {feed_a[0]:.3f} {feed_a[1]:.3f}) '
        f'(size 0.7 0.7) (layers "F.Cu" "F.Paste" "F.Mask"))'
    )
    lines.append(
        f'  (pad "2" smd rect (at {feed_b[0]:.3f} {feed_b[1]:.3f}) '
        f'(size 0.7 0.7) (layers "F.Cu" "F.Paste" "F.Mask"))'
    )
    lines.append(
        f'  (fp_line (start {feed_a[0]:.3f} {feed_a[1]:.3f}) (end {feed_b[0]:.3f} {feed_b[1]:.3f}) '
        f'(layer "F.Cu") (stroke (width {ANT_TRACE}) (type solid)))'
    )
    lines.append(")\n")
    (PRETTY / "PCB_Antenna_RoundSpiral.kicad_mod").write_text("\n".join(lines))
    old = PRETTY / "PCB_Antenna_RectSpiral.kicad_mod"
    if old.exists():
        old.unlink()


def write_tables() -> None:
    (ROOT / "sym-lib-table").write_text(
        """(sym_lib_table
  (version 7)
  (lib (name "tinynfc")(type "KiCad")(uri "${KIPRJMOD}/libraries/tinynfc.kicad_sym")(options "")(descr "TinyNFC project symbols"))
)
"""
    )
    (ROOT / "fp-lib-table").write_text(
        """(fp_lib_table
  (version 7)
  (lib (name "tinynfc")(type "KiCad")(uri "${KIPRJMOD}/libraries/tinynfc.pretty")(options "")(descr "TinyNFC project footprints"))
)
"""
    )


def write_project_file() -> None:
    # Minimal KiCad 7 project JSON.
    pro = {
        "board": {
            "design_settings": {
                "defaults": {
                    "board_outline_line_width": 0.1,
                    "copper_line_width": 0.2,
                    "copper_text_size_h": 1.0,
                    "copper_text_size_v": 1.0,
                    "copper_text_thickness": 0.15,
                    "other_line_width": 0.15,
                    "silk_line_width": 0.12,
                    "silk_text_size_h": 1.0,
                    "silk_text_size_v": 1.0,
                    "silk_text_thickness": 0.12,
                },
                "rules": {
                    "min_copper_edge_clearance": 0.2,
                    "min_hole_clearance": 0.25,
                    "min_hole_to_hole": 0.25,
                    "min_microvia_diameter": 0.2,
                    "min_microvia_drill": 0.1,
                    "min_resolved_spokes": 2,
                    "min_silk_clearance": 0.0,
                    "min_text_height": 0.8,
                    "min_text_thickness": 0.08,
                    "min_through_hole_diameter": 0.3,
                    "min_track_width": 0.15,
                    "min_via_annular_width": 0.1,
                    "min_via_diameter": 0.4,
                    "solder_mask_clearance": 0.0,
                    "solder_mask_min_width": 0.0,
                },
                "track_widths": [0.15, 0.2, 0.3, 0.5],
                "via_dimensions": [{"diameter": 0.6, "drill": 0.3}],
            },
            "layer_presets": [],
            "viewports": [],
        },
        "boards": [],
        "cvpcb": {"equivalence_files": []},
        "libraries": {"pinned_footprint_libs": [], "pinned_symbol_libs": []},
        "meta": {"filename": "tinynfc.kicad_pro", "version": 1},
        "net_settings": {
            "classes": [
                {
                    "bus_width": 12,
                    "clearance": 0.2,
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
                    "via_diameter": 0.6,
                    "via_drill": 0.3,
                    "wire_width": 6,
                }
            ],
            "meta": {"version": 3},
            "net_colors": None,
            "netclass_assignments": None,
            "netclass_patterns": [],
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
                "dashed_lines_dash_length_ratio": 12.0,
                "dashed_lines_gap_length_ratio": 3.0,
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
            "spice_current_sheet_as_root": False,
            "spice_external_command": 'spice "%I"',
            "spice_model_current_sheet_as_root": True,
            "spice_save_all_currents": False,
            "spice_save_all_voltages": False,
            "subpart_first_id": 65,
            "subpart_id_separator": 0,
        },
        "sheets": [["ROOT_UUID", "Root"]],
        "text_variables": {},
    }
    # placeholder replaced after schematic UUID known
    (ROOT / "tinynfc.kicad_pro").write_text(json.dumps(pro, indent=2) + "\n")


# ---------------------------------------------------------------------------
# Schematic
# ---------------------------------------------------------------------------

def copy_sym(lib: str, name: str) -> str:
    path = Path(f"/usr/share/kicad/symbols/{lib}.kicad_sym")
    block = extract_system_symbol(path, name)
    # Only the top-level symbol gets the library prefix. Unit bodies stay Name_0_1.
    return block.replace(f'(symbol "{name}"', f'(symbol "{lib}:{name}"', 1)


def sch_component(
    lib_id: str,
    ref: str,
    value: str,
    footprint: str,
    x: float,
    y: float,
    rotation: int,
    pins: list[str],
    root_uuid: str,
    extras: str = "",
) -> str:
    pin_block = "\n".join(f'    (pin "{p}" (uuid {uid()}))' for p in pins)
    return f'''  (symbol (lib_id "{lib_id}") (at {x} {y} {rotation}) (unit 1)
    (in_bom yes) (on_board yes) (dnp no)
    (uuid {uid()})
    (property "Reference" "{ref}" (at {x} {y - 5.08} {rotation})
      (effects (font (size 1.27 1.27))))
    (property "Value" "{value}" (at {x} {y + 5.08} {rotation})
      (effects (font (size 1.27 1.27))))
    (property "Footprint" "{footprint}" (at {x} {y} {rotation})
      (effects (font (size 1.27 1.27)) hide))
    (property "Datasheet" "" (at {x} {y} {rotation})
      (effects (font (size 1.27 1.27)) hide))
{extras}{pin_block}
    (instances
      (project "tinynfc"
        (path "/{root_uuid}"
          (reference "{ref}")
          (unit 1)
        )
      )
    )
  )
'''


def sch_label(name: str, x: float, y: float, rot: int = 0) -> str:
    return f'''  (label "{name}"
    (at {x} {y} {rot})
    (effects (font (size 1.27 1.27)) (justify left bottom))
    (uuid {uid()})
  )
'''


def sch_nc(x: float, y: float) -> str:
    return f'''  (no_connect (at {x} {y}) (uuid {uid()}))
'''


def sch_text(text: str, x: float, y: float, size: float = 2.0) -> str:
    return f'''  (text "{text}"
    (at {x} {y} 0)
    (effects (font (size {size} {size})))
    (uuid {uid()})
  )
'''


def write_schematic() -> str:
    root_uuid = uid()
    # Embed commonly used symbols from system libs + project symbols.
    lib_symbols = []
    for lib, name in [
        ("Device", "R"),
        ("Device", "C"),
        ("Device", "L"),
        ("Device", "Q_PMOS_GSD"),
        ("Device", "Buzzer"),
        ("Device", "D"),
        ("Connector", "TestPoint"),
        ("power", "GND"),
        ("power", "PWR_FLAG"),
    ]:
        lib_symbols.append(copy_sym(lib, name))

    # Project symbols with tinynfc: prefix (top-level only; unit bodies keep bare names)
    nt3 = NT3H_SYMBOL.replace('(symbol "NT3H2111W0FHKH"', '(symbol "tinynfc:NT3H2111W0FHKH"', 1)
    mcu = Path("/tmp/attiny_sym.txt").read_text()
    mcu = mcu.replace('(symbol "ATtiny816-MNR"', '(symbol "tinynfc:ATtiny816-MNR"', 1)
    lib_symbols.append(nt3)
    lib_symbols.append(mcu)

    comps: list[str] = []
    labels: list[str] = []
    ncs: list[str] = []
    texts: list[str] = []

    texts.append(sch_text("TinyNFC — NFC energy-harvesting audio player", 25.4, 20.32, 2.54))
    texts.append(
        sch_text(
            "Hard-tied C on VOUT must stay under 220 nF. Bulk 10 uF is FET-gated.",
            25.4,
            25.4,
            1.27,
        )
    )

    # --- NFC / antenna block (left) ---
    comps.append(
        sch_component(
            "tinynfc:NT3H2111W0FHKH",
            "U1",
            "NT3H2111W0FHKH",
            "tinynfc:NXP_SOT902-3_XQFN8",
            63.5,
            63.5,
            0,
            [str(i) for i in range(1, 9)],
            root_uuid,
        )
    )
    comps.append(
        sch_component(
            "Device:L",
            "L1",
            "2.75uH",
            "tinynfc:PCB_Antenna_RoundSpiral",
            33.02,
            53.34,
            0,
            ["1", "2"],
            root_uuid,
            extras='    (property "Description" "PCB spiral antenna target inductance" (at 33.02 53.34 0)\n      (effects (font (size 1.27 1.27)) hide))\n',
        )
    )
    comps.append(
        sch_component(
            "Device:C",
            "C1",
            "1.5pF",
            "Capacitor_SMD:C_0402_1005Metric",
            33.02,
            68.58,
            0,
            ["1", "2"],
            root_uuid,
        )
    )

    labels += [
        sch_label("LA", 25.4, 50.8),
        sch_label("LB", 25.4, 55.88),
        sch_label("LA", 50.8, 58.42),
        sch_label("LB", 76.2, 63.5),
        sch_label("VOUT", 76.2, 58.42),
        sch_label("VOUT", 63.5, 50.8),  # NTAG VCC tied to VOUT
        sch_label("GND", 63.5, 76.2),
    ]
    ncs += [
        sch_nc(50.8, 63.5),  # SCL
        sch_nc(50.8, 68.58),  # FD
        sch_nc(76.2, 68.58),  # SDA
    ]

    # --- Power / delayed bulk ---
    comps.append(
        sch_component(
            "Device:C",
            "C2",
            "100nF",
            "Capacitor_SMD:C_0402_1005Metric",
            101.6,
            50.8,
            0,
            ["1", "2"],
            root_uuid,
            extras='    (property "Description" "Hard-tied VOUT bulk; keep total <220nF" (at 101.6 50.8 0)\n      (effects (font (size 1.27 1.27)) hide))\n',
        )
    )
    comps.append(
        sch_component(
            "Device:Q_PMOS_GSD",
            "Q1",
            "DMP21D0UFB4",
            "Package_DFN_QFN:Diodes_DFN1006-3",
            114.3,
            63.5,
            0,
            ["1", "2", "3"],
            root_uuid,
        )
    )
    comps.append(
        sch_component(
            "Device:R",
            "R1",
            "100k",
            "Resistor_SMD:R_0402_1005Metric",
            101.6,
            63.5,
            0,
            ["1", "2"],
            root_uuid,
        )
    )
    comps.append(
        sch_component(
            "Device:R",
            "R2",
            "2.2k",
            "Resistor_SMD:R_0402_1005Metric",
            127.0,
            71.12,
            0,
            ["1", "2"],
            root_uuid,
        )
    )
    comps.append(
        sch_component(
            "Device:C",
            "C3",
            "10uF",
            "Capacitor_SMD:C_0402_1005Metric",
            127.0,
            50.8,
            0,
            ["1", "2"],
            root_uuid,
            extras='    (property "Description" "Gated bulk reservoir after ~120ms" (at 127.0 50.8 0)\n      (effects (font (size 1.27 1.27)) hide))\n',
        )
    )
    labels += [
        sch_label("VOUT", 96.52, 45.72),
        sch_label("GND", 101.6, 58.42),
        sch_label("VOUT", 106.68, 58.42),  # R1 to VOUT / Q1 source
        sch_label("CAP_GATE", 114.3, 71.12),
        sch_label("CAP_EN", 134.62, 71.12),
        sch_label("VBULK", 134.62, 45.72),
        sch_label("GND", 127.0, 58.42),
        sch_label("VOUT", 114.3, 55.88),
    ]

    # --- MCU ---
    comps.append(
        sch_component(
            "tinynfc:ATtiny816-MNR",
            "U2",
            "ATtiny816-MNR",
            "Package_DFN_QFN:VQFN-20-1EP_3x3mm_P0.4mm_EP1.7x1.7mm",
            177.8,
            63.5,
            0,
            [str(i) for i in range(1, 22)],
            root_uuid,
        )
    )
    labels += [
        sch_label("VOUT", 177.8, 38.1),
        sch_label("GND", 177.8, 88.9),
        sch_label("UPDI", 195.58, 43.18),
        sch_label("CAP_EN", 195.58, 63.5),
        sch_label("PIEZO_A", 195.58, 71.12),
        sch_label("PIEZO_B", 195.58, 76.2),
    ]
    # Unused MCU pins -> NC (PA1-6, PB2-5, PC0-3, PA2, PA3)
    for y in [45.72, 48.26, 50.8, 53.34, 55.88, 58.42, 80.0, 82.54, 85.08]:
        ncs.append(sch_nc(195.58, y))

    # --- Piezo ---
    comps.append(
        sch_component(
            "Device:R",
            "R3",
            "220",
            "Resistor_SMD:R_0402_1005Metric",
            220.98,
            71.12,
            0,
            ["1", "2"],
            root_uuid,
        )
    )
    comps.append(
        sch_component(
            "Device:Buzzer",
            "PZ1",
            "FUET-9018",
            "Buzzer_Beeper:Buzzer_Murata_PKMCS0909E",
            241.3,
            76.2,
            0,
            ["1", "2"],
            root_uuid,
            extras='    (property "Description" "9x9 passive piezo; PKMCS0909 land pattern" (at 241.3 76.2 0)\n      (effects (font (size 1.27 1.27)) hide))\n',
        )
    )
    labels += [
        sch_label("PIEZO_A", 210.82, 71.12),
        sch_label("PIEZO_P", 228.6, 71.12),
        sch_label("PIEZO_P", 233.68, 71.12),
        sch_label("PIEZO_B", 233.68, 81.28),
    ]

    # --- Programming / ESD ---
    comps.append(
        sch_component(
            "Connector:TestPoint",
            "TP1",
            "GND",
            "TestPoint:TestPoint_Pad_D1.0mm",
            101.6,
            101.6,
            0,
            ["1"],
            root_uuid,
        )
    )
    comps.append(
        sch_component(
            "Connector:TestPoint",
            "TP2",
            "VCC",
            "TestPoint:TestPoint_Pad_D1.0mm",
            111.76,
            101.6,
            0,
            ["1"],
            root_uuid,
        )
    )
    comps.append(
        sch_component(
            "Connector:TestPoint",
            "TP3",
            "UPDI",
            "TestPoint:TestPoint_Pad_D1.0mm",
            121.92,
            101.6,
            0,
            ["1"],
            root_uuid,
        )
    )
    comps.append(
        sch_component(
            "Device:D",
            "D1",
            "TPESD8L3_3CT5G",
            "Diode_SMD:D_SOD-882",
            137.16,
            101.6,
            0,
            ["1", "2"],
            root_uuid,
            extras='    (property "Description" "UPDI ESD TVS to GND" (at 137.16 101.6 0)\n      (effects (font (size 1.27 1.27)) hide))\n',
        )
    )
    labels += [
        sch_label("GND", 101.6, 96.52),
        sch_label("VOUT", 111.76, 96.52),
        sch_label("UPDI", 121.92, 96.52),
        sch_label("UPDI", 132.08, 96.52),
        sch_label("GND", 142.24, 106.68),
    ]

    # Power flags
    comps.append(
        sch_component(
            "power:PWR_FLAG",
            "#FLG01",
            "PWR_FLAG",
            "",
            88.9,
            45.72,
            0,
            ["1"],
            root_uuid,
        )
    )
    labels.append(sch_label("VOUT", 88.9, 40.64))
    comps.append(
        sch_component(
            "power:GND",
            "#PWR01",
            "GND",
            "",
            88.9,
            88.9,
            0,
            ["1"],
            root_uuid,
        )
    )

    texts.append(
        sch_text(
            "Pin map: PA7=CAP_EN, PB0=PIEZO_A (TCA0 WO0), PB1=PIEZO_B, PA0=UPDI",
            152.4,
            101.6,
            1.27,
        )
    )
    texts.append(
        sch_text(
            "Place electronics in antenna center island. No GND pour under spiral.",
            152.4,
            106.68,
            1.27,
        )
    )

    content = f'''(kicad_sch (version 20230121) (generator tinynfc-generate)
  (uuid {root_uuid})
  (paper "A3")
  (title_block
    (title "TinyNFC")
    (date "2026-08-31")
    (rev "0.1")
    (company "")
    (comment 1 "Batteryless NFC-powered chiptune PCB")
    (comment 2 "See tinynfc/design.md")
  )
  (lib_symbols
{chr(10).join(lib_symbols)}
  )
{"".join(texts)}
{"".join(comps)}
{"".join(labels)}
{"".join(ncs)}
  (sheet_instances
    (path "/" (page "1"))
  )
)
'''
    (ROOT / "tinynfc.kicad_sch").write_text(content)
    # Update project sheet UUID
    pro_path = ROOT / "tinynfc.kicad_pro"
    pro = json.loads(pro_path.read_text())
    pro["sheets"] = [[root_uuid, "Root"]]
    pro_path.write_text(json.dumps(pro, indent=2) + "\n")
    return root_uuid


# ---------------------------------------------------------------------------
# PCB
# ---------------------------------------------------------------------------

def add_fp(board: pcbnew.BOARD, libpath: str, name: str, ref: str, x_mm: float, y_mm: float, rot_deg: float = 0):
    fp = pcbnew.FootprintLoad(libpath, name)
    if fp is None:
        raise RuntimeError(f"cannot load {libpath}:{name}")
    fp.SetReference(ref)
    fp.SetPosition(pcbnew.VECTOR2I(mm(x_mm), mm(y_mm)))
    fp.SetOrientationDegrees(rot_deg)
    # Dense postage-stamp layout: keep ref/value off silk so they never sit on copper.
    fp.Reference().SetVisible(False)
    fp.Value().SetVisible(False)
    board.Add(fp)
    return fp


def draw_round_outline(board: pcbnew.BOARD, diameter: float) -> None:
    r = diameter / 2
    circ = pcbnew.PCB_SHAPE(board)
    circ.SetShape(pcbnew.SHAPE_T_CIRCLE)
    circ.SetLayer(pcbnew.Edge_Cuts)
    circ.SetCenter(pcbnew.VECTOR2I(mm(0), mm(0)))
    circ.SetEnd(pcbnew.VECTOR2I(mm(r), mm(0)))
    circ.SetWidth(mm(0.1))
    board.Add(circ)


def add_keepout_zone(board: pcbnew.BOARD, _size: float) -> None:
    """Forbid copper pours under the antenna area (no GND pour on this board)."""
    # We simply do not add a GND zone. Document a circular keepout for the spiral.
    r = ANT_OUTER_DIA / 2 + 0.5
    ko = pcbnew.ZONE(board)
    ko.SetIsRuleArea(True)
    ko.SetDoNotAllowTracks(False)
    ko.SetDoNotAllowVias(False)
    ko.SetDoNotAllowPads(False)
    ko.SetDoNotAllowCopperPour(True)
    ko.SetDoNotAllowFootprints(False)
    ko.SetLayerSet(pcbnew.LSET.AllCuMask())
    outline = ko.Outline()
    outline.NewOutline()
    for i in range(64):
        ang = 2 * math.pi * i / 64
        outline.Append(pcbnew.VECTOR2I(mm(r * math.cos(ang)), mm(r * math.sin(ang))))
    board.Add(ko)


def add_quarter_scale(board: pcbnew.BOARD) -> None:
    """Draw a US-quarter outline on Dwgs.User, beside the board, for scale."""
    r = US_QUARTER_DIA_MM / 2
    # Sit to the right of the round outline with a small gap.
    cx = BOARD_DIA_MM / 2 + 2.0 + r
    cy = 0.0
    circ = pcbnew.PCB_SHAPE(board)
    circ.SetShape(pcbnew.SHAPE_T_CIRCLE)
    circ.SetLayer(pcbnew.Dwgs_User)
    circ.SetCenter(pcbnew.VECTOR2I(mm(cx), mm(cy)))
    circ.SetEnd(pcbnew.VECTOR2I(mm(cx + r), mm(cy)))
    circ.SetWidth(mm(0.15))
    board.Add(circ)
    for txt, x, y, h in [
        ("US quarter", cx, cy - r - 2.2, 1.0),
        (f"Ø{US_QUARTER_DIA_MM} mm", cx, cy - r - 0.9, 0.8),
        (f"board Ø{BOARD_DIA_MM:.0f}×{BOARD_THICKNESS_MM} mm", 0.0, -BOARD_DIA_MM / 2 - 2.4, 0.9),
        (f"assembled ~{BOARD_THICKNESS_MM + PIEZO_HEIGHT_MM:.1f} mm tall", 0.0, -BOARD_DIA_MM / 2 - 1.2, 0.7),
    ]:
        t = pcbnew.PCB_TEXT(board)
        t.SetText(txt)
        t.SetPosition(pcbnew.VECTOR2I(mm(x), mm(y)))
        t.SetLayer(pcbnew.Dwgs_User)
        t.SetTextHeight(mm(h))
        t.SetTextWidth(mm(h))
        t.SetTextThickness(mm(max(0.1, h * 0.12)))
        board.Add(t)


def write_pcb() -> None:
    board = pcbnew.BOARD()
    # Title
    board.GetTitleBlock().SetTitle("TinyNFC")
    board.GetTitleBlock().SetDate("2026-08-31")
    board.GetTitleBlock().SetRevision("0.3")
    board.GetTitleBlock().SetComment(0, "NFC energy-harvesting audio player")

    draw_round_outline(board, BOARD_DIA_MM)
    add_keepout_zone(board, BOARD_DIA_MM)
    add_quarter_scale(board)

    sys_fp = "/usr/share/kicad/footprints"
    # Antenna fills the disc; electronics sit in the center island.
    add_fp(board, str(PRETTY), "PCB_Antenna_RoundSpiral", "L1", 0, 0, 0)

    # 9×9 mm piezo at origin; silicon and 0402s ring the body inside the spiral.
    add_fp(board, f"{sys_fp}/Buzzer_Beeper.pretty", "Buzzer_Murata_PKMCS0909E", "PZ1", 0.0, 0.0, 0)
    add_fp(board, str(PRETTY), "NXP_SOT902-3_XQFN8", "U1", -5.2, -5.8, 0)
    add_fp(
        board,
        f"{sys_fp}/Package_DFN_QFN.pretty",
        "VQFN-20-1EP_3x3mm_P0.4mm_EP1.7x1.7mm",
        "U2",
        4.8,
        -5.8,
        0,
    )
    add_fp(board, f"{sys_fp}/Package_DFN_QFN.pretty", "Diodes_DFN1006-3", "Q1", -5.4, 5.6, 0)
    add_fp(board, f"{sys_fp}/Capacitor_SMD.pretty", "C_0402_1005Metric", "C1", -5.2, -3.6, 0)
    add_fp(board, f"{sys_fp}/Capacitor_SMD.pretty", "C_0402_1005Metric", "C2", -3.4, 5.6, 0)
    add_fp(board, f"{sys_fp}/Capacitor_SMD.pretty", "C_0402_1005Metric", "C3", -1.6, 5.6, 0)
    add_fp(board, f"{sys_fp}/Resistor_SMD.pretty", "R_0402_1005Metric", "R1", 0.2, 5.8, 0)
    add_fp(board, f"{sys_fp}/Resistor_SMD.pretty", "R_0402_1005Metric", "R2", 2.0, 5.8, 0)
    add_fp(board, f"{sys_fp}/Resistor_SMD.pretty", "R_0402_1005Metric", "R3", 5.4, 5.4, 90)
    add_fp(board, f"{sys_fp}/Diode_SMD.pretty", "D_SOD-882", "D1", 5.6, -3.4, 0)

    # UPDI pogo pads in the south margin inside the circular outline (1.0 mm pads).
    y_pads = BOARD_DIA_MM / 2 - 1.6
    add_fp(board, f"{sys_fp}/TestPoint.pretty", "TestPoint_Pad_D1.0mm", "TP1", -2.54, y_pads, 0)
    add_fp(board, f"{sys_fp}/TestPoint.pretty", "TestPoint_Pad_D1.0mm", "TP2", 0.0, y_pads, 0)
    add_fp(board, f"{sys_fp}/TestPoint.pretty", "TestPoint_Pad_D1.0mm", "TP3", 2.54, y_pads, 0)

    # Silk only for pad callouts — kept clear of antenna copper.
    for txt, x, y in [
        ("GND", -2.54, y_pads + 1.1),
        ("VCC", 0.0, y_pads + 1.1),
        ("UPDI", 2.54, y_pads + 1.1),
    ]:
        t = pcbnew.PCB_TEXT(board)
        t.SetText(txt)
        t.SetPosition(pcbnew.VECTOR2I(mm(x), mm(y)))
        t.SetLayer(pcbnew.F_SilkS)
        t.SetTextHeight(mm(0.6))
        t.SetTextWidth(mm(0.6))
        t.SetTextThickness(mm(0.1))
        board.Add(t)

    out = ROOT / "tinynfc.kicad_pcb"
    board.Save(str(out))
    print(f"wrote {out}")


def write_readme() -> None:
    (ROOT / "README.md").write_text(
        """# TinyNFC KiCad project

KiCad 7 schematic and PCB for the batteryless NFC energy-harvesting audio
player described in [`../design.md`](../design.md).

## Open the project

```bash
kicad tinynfc/kicad/tinynfc.kicad_pro
```

Requires KiCad 7 or later with the standard symbol/footprint libraries.

## What's in the design

| Ref | Part | Role |
|-----|------|------|
| U1 | NT3H2111W0FHKH | NFC harvest (`VOUT`) + antenna |
| L1 | PCB spiral | ~2.75 µH circular spiral on `F.Cu` |
| C1 | 1.5 pF 0402 | Antenna fine tune |
| C2 | 100 nF 0402 | Hard-tied `VOUT` bypass (<220 nF limit) |
| Q1 | DMP21D0UFB4 | P-FET gate for delayed bulk cap |
| R1 | 100 kΩ | Gate pull-up (FET off at field entry) |
| R2 | 2.2 kΩ | Gate series limit from `CAP_EN` |
| C3 | 10 µF 0402 | Gated bulk reservoir on `VBULK` |
| U2 | ATtiny816-MNR | Melody PWM + gate control |
| R3 | 220 Ω | Piezo series current limit |
| PZ1 | FUET-9018 | Passive 9×9 piezo (PKMCS0909 land) |
| D1 | TPESD8L3_3CT5G | UPDI ESD TVS |
| TP1–TP3 | 1.0 mm pads @ 2.54 mm | GND / VCC / UPDI pogo |

### MCU pin map

| Net | Pin | Function |
|-----|-----|----------|
| `UPDI` | PA0 | Programming |
| `CAP_EN` | PA7 | Drive P-FET gate low after ~120 ms |
| `PIEZO_A` | PB0 | TCA0 WO0 |
| `PIEZO_B` | PB1 | Complementary drive |

NTAG `VCC` is tied to `VOUT` (self-powered). `SCL` / `SDA` / `FD` are unused
in this revision (no-connects).

## Layout rules

- Board: **Ø 28 mm × 1.6 mm** round postage stamp (not credit-card size). A
  larger outline couples more RF; this one is the minimum that still fits a
  9 mm piezo in the spiral island plus UPDI pads in the edge margin.
- Thickness: **1.6 mm** FR-4 by default (~**3.4 mm** assembled with the piezo).
  Optional 0.8 mm FR-4 for a flatter button.
- Antenna: Ø 24 mm circular spiral, 6 turns, 0.35 / 0.28 mm trace/gap on
  `F.Cu`. Do **not** add a continuous GND plane under it.
- A US-quarter outline (Ø 24.26 mm) is drawn on `Dwgs.User` beside the board
  for scale — documentation only, not fab copper.
- Footprint reference designators are hidden on silk so they do not sit on
  copper. Only GND / VCC / UPDI pad labels are silkscreened.
- Keep the piezo + gated bulk path short inside the spiral island.

## Regenerate

```bash
python3 tinynfc/kicad/scripts/generate_project.py
```

Schematic connectivity uses net labels. After opening in KiCad, run **Update
PCB from Schematic**, then route the ratsnest. The generator places footprints
but does not auto-route.

## Status

Draft for requirements iteration. Not fabrication-ready: confirm antenna
inductance on the VNA, FET/TVS land patterns against manufacturer drawings,
and run ERC/DRC in KiCad before ordering boards.
"""
    )


def main() -> None:
    write_symbol_library()
    write_xqfn8_footprint()
    write_antenna_footprint()
    write_tables()
    write_project_file()
    write_schematic()
    write_pcb()
    write_readme()
    print("TinyNFC KiCad project generated in", ROOT)


if __name__ == "__main__":
    main()
