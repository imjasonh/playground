# KiCad 8/9 Schematic S-Expression Format Reference

## File Structure

```
(kicad_sch
  (version 20231120)
  (generator "name")
  (generator_version "8.0")
  (uuid "...")
  (paper "A1")
  (title_block ...)

  (lib_symbols
    ;; Embedded symbol definitions (copied from .kicad_sym libraries)
    (symbol "Library:SymbolName" ...)
  )

  ;; Placed components, wires, labels, etc.
  (symbol (lib_id "Library:SymbolName") (at X Y ANGLE) ...)
  (wire (pts (xy X1 Y1) (xy X2 Y2)) ...)
  (label "NetName" (at X Y ANGLE) ...)
  (no_connect (at X Y) ...)

  (sheet_instances
    (path "/" (page "1"))
  )
)
```

## Coordinate System

- **Units**: millimeters
- **X axis**: positive = right
- **Y axis**: positive = DOWN (screen convention)
- **Default grid**: 1.27 mm (50 mil)
- **Angles**: degrees, counterclockwise (0=right, 90=up, 180=left, 270=down)

### Library vs Schematic Y-axis (CRITICAL)

Symbol libraries (.kicad_sym) use **Y-up** (math convention).
Schematics (.kicad_sch) use **Y-down** (screen convention).

**This is the #1 source of bugs in generated schematics.** If you forget to negate Y when transforming from library to schematic coordinates, every label and wire endpoint will be wrong.

When a symbol is placed at (sx, sy) with rotation R, a pin at library position (px, py) maps to:
- **Rotation 0**:   schematic (sx + px, sy **- py**)  <- note the negation
- **Rotation 90**:  schematic (sx + py, sy + px)
- **Rotation 180**: schematic (sx - px, sy + py)
- **Rotation 270**: schematic (sx - py, sy - px)

### Worked Example

AD9363 placed at schematic (320, 200) with rotation 0.
Pin TX1A_P at library position (-17.78, 25.40).

Schematic position = (320 + (-17.78), 200 - 25.40) = **(302.22, 174.60)**

Common mistake: using (320 + (-17.78), 200 + 25.40) = (302.22, **225.40**) — this is 50.8mm off in Y!

### Grid Snapping

All coordinates MUST be multiples of 1.27mm (the default 50-mil grid). Off-grid coordinates cause `endpoint_off_grid` warnings that cascade through all connected wires and labels.

```python
GRID = 1.27
def snap(v):
    return round(v / GRID) * GRID
```

Apply `snap()` to every coordinate: component positions, wire endpoints, label positions, no-connect positions.

## Embedded lib_symbols Section

Every symbol used in the schematic must be defined in `(lib_symbols ...)`.
These are copies from the library files, embedded for portability.

### Critical Rule: Sub-symbol Naming

Parent symbols use the full library-prefixed name: `(symbol "Device:R" ...)`
Sub-symbols (for units and body styles) must NOT include the library prefix:
- CORRECT: `(symbol "R_0_1" ...)` and `(symbol "R_1_1" ...)`
- WRONG: `(symbol "Device:R_0_1" ...)` <- causes "Invalid symbol unit name prefix" error

The naming convention is: `{SymbolName}_{unit}_{bodystyle}`
- `_0_1`: Body style drawings (rectangles, lines, arcs)
- `_1_1`: Pin definitions for unit 1

**Why this matters:** KiCad will open the file without complaining, but symbols will appear as broken boxes with no visible pins. The sub-symbol names must match what KiCad expects internally.

**Fix with regex post-processing:**
```python
import re

def fix_subsymbol_names(content):
    """Remove library prefixes from sub-symbol names inside lib_symbols."""
    def fix_match(m):
        lib_prefix = m.group(1)   # e.g., "Device:"
        sym_name = m.group(2)     # e.g., "R"
        suffix = m.group(3)       # e.g., "_0_1" or "_1_1"
        return f'(symbol "{sym_name}{suffix}"'
    # Match sub-symbols that incorrectly have a library prefix
    pattern = r'\(symbol "([A-Za-z_][A-Za-z0-9_-]*):([A-Za-z_][A-Za-z0-9_-]*)(_\d+_\d+)"'
    return re.sub(pattern, fix_match, content)
```

### Pin Definition Format

```
(pin TYPE STYLE (at X Y ANGLE) (length L)
  (name "PinName" (effects (font (size 1.0 1.0))))
  (number "PinNum" (effects (font (size 1.0 1.0)))))
```

- TYPE: passive, power_in, power_out, input, output, bidirectional
- STYLE: line, inverted, clock, etc.
- (at X Y ANGLE): Connection point position in **library coordinates (Y-up)**
- ANGLE: Direction the pin points INTO the symbol body
  - 0 = pin points right (connection is on LEFT side)
  - 90 = pin points up (connection is on BOTTOM)
  - 180 = pin points left (connection is on RIGHT side)
  - 270 = pin points down (connection is on TOP)

### Standard 2-Pin Passive Symbol Positions

KiCad's standard Device:R, Device:C, Device:L symbols have:
- Pin 1 at library (0, 2.54) — becomes schematic (sx, sy - 2.54) = TOP
- Pin 2 at library (0, -2.54) — becomes schematic (sx, sy + 2.54) = BOTTOM

### SOT-23-5 Package Pin Positions (Common LDOs)

For AP2112K, ME6211, and similar SOT-23-5 LDOs:

| Pin | Name | Library Position | Schematic Position (rot=0) |
|-----|------|-----------------|---------------------------|
| 1   | VIN  | (-7.62, 2.54)   | (sx - 7.62, sy - 2.54)   |
| 2   | GND  | (0, -7.62)      | (sx, sy + 7.62)           |
| 3   | EN   | (-7.62, -2.54)  | (sx - 7.62, sy + 2.54)   |
| 4   | NC   | (7.62, -2.54)   | (sx + 7.62, sy + 2.54)   |
| 5   | VOUT | (7.62, 2.54)    | (sx + 7.62, sy - 2.54)   |

**WARNING:** VOUT (pin 5) and NC (pin 4) are at the same X but differ only in Y sign. After the Y-flip transform, VOUT is at sy - 2.54 (above center) and NC is at sy + 2.54 (below center). Confusing them makes the LDO output go to a no-connect instead of the power rail.

## Placed Symbol Format

```
(symbol (lib_id "Library:Name") (at X Y ANGLE) [mirror]
  (uuid "...")
  (property "Reference" "U1" (at X Y 0) (effects ...))
  (property "Value" "IC_Name" (at X Y 0) (effects ...))
  (property "Footprint" "Package:FP" (at X Y 0) (effects ... hide))
  (instances
    (project "project_name"
      (path "/ROOT_UUID"
        (reference "U1")
        (unit 1)
      )
    )
  )
)
```

Required fields: lib_id, at, uuid, Reference, Value, Footprint, instances.

The `(at X Y ANGLE)` positions must be on the 1.27mm grid.

## Wire Format

```
(wire (pts (xy X1 Y1) (xy X2 Y2))
  (stroke (width 0) (type default))
  (uuid "...")
)
```

Wires connect components via their pin endpoints. A wire endpoint must
**exactly coincide** with a pin's connection point to make a connection.
Even a 0.01mm mismatch will cause an ERC error. Always compute wire
endpoints from pin positions, never guess them.

## Label Format

```
(label "NetName" (at X Y ANGLE)
  (effects (font (size 1.27 1.27)) (justify left))
  (uuid "...")
)
```

A label must be placed at a wire endpoint or directly at a pin's
connection point. Labels at coordinates that don't match any wire
or pin will cause "label_dangling" ERC errors.

**Label angle conventions:**
- 0 = text reads left-to-right, label connects on the LEFT
- 90 = text reads bottom-to-top, label connects on the BOTTOM
- 180 = text reads right-to-left, label connects on the RIGHT
- 270 = text reads top-to-bottom, label connects on the TOP

Choose the angle so the label text doesn't overlap the component body.

## Power Symbol Format

Power symbols (GND, VCC) are special symbols with the `(power)` flag.
They have a single pin that defines the power net.

```
(symbol (lib_id "power:GND") (at X Y 0)
  (uuid "...")
  (property "Reference" "#PWR0XX" (at X Y+2.54 0)
    (effects (font (size 1.27 1.27)) hide))
  (property "Value" "GND" (at X Y+1.27 0)
    (effects (font (size 1.27 1.27))))
  (property "Footprint" "" (at X Y 0)
    (effects (font (size 1.27 1.27)) hide))
  (pin "1" (uuid "..."))
  (instances ...)
)
```

Power symbols automatically create the named net (e.g., "GND", "VCC").

## No-Connect Flag

```
(no_connect (at X Y)
  (uuid "...")
)
```

Place at pin connection points for intentionally unconnected pins.
The (at X Y) must exactly match the pin's schematic position (computed
using the transform formula, not guessed).

## PWR_FLAG

To avoid "power_pin_not_driven" errors, place PWR_FLAG symbols on nets
that are driven by components that KiCad doesn't recognize as power sources
(e.g., voltage regulators with passive output pins).

**When to add PWR_FLAG:**
- Every voltage regulator output net (LDO VOUT, switching regulator output)
- GND net if no dedicated GND power symbol is used
- Any net where all connected power_in pins have no power_out driver

Define PWR_FLAG in lib_symbols:
```
(symbol "power:PWR_FLAG"
  (power) (pin_numbers hide) (pin_names hide) (in_bom no) (on_board yes)
  (property "Reference" "#FLG" (at 0 2.54 0) (effects (font (size 1.27 1.27)) hide))
  (property "Value" "PWR_FLAG" (at 0 3.81 0) (effects (font (size 1.0 1.0))))
  (property "Footprint" "" (at 0 0 0) (effects (font (size 1.27 1.27)) hide))
  (symbol "PWR_FLAG_0_1"
    (polyline (pts (xy 0 0) (xy 0 1.27) (xy -1.016 2.032) (xy 0 2.794) (xy 1.016 2.032) (xy 0 1.27))
      (stroke (width 0) (type default)) (fill (type none)))
  )
  (symbol "PWR_FLAG_1_1"
    (pin power_out line (at 0 0 90) (length 0)
      (name "pwr" (effects (font (size 1.0 1.0))))
      (number "1" (effects (font (size 1.0 1.0)))))
  )
)
```

Note: PWR_FLAG sub-symbols use unprefixed names (`PWR_FLAG_0_1`, not `power:PWR_FLAG_0_1`).

## Parenthesis Balance

KiCad S-expression files must have perfectly balanced parentheses. An imbalance will cause the file to fail to open or to be parsed incorrectly.

Always verify after generation:
```python
depth = sum(1 if c == '(' else -1 if c == ')' else 0 for c in content)
assert depth == 0, f"Parenthesis imbalance: depth={depth}"
```

## Common ERC Error Types

| Error Type | Severity | Cause | Fix |
|---|---|---|---|
| pin_not_connected | error | Pin has no wire/label/no-connect | Add wire+label or no_connect at exact pin position |
| label_dangling | error | Label not at wire/pin endpoint | Move label to computed pin position using transform formula |
| power_pin_not_driven | error | Power input with no power source | Add PWR_FLAG on the net |
| pin_not_driven | error | Input pin with no output driver | Connect to output or add pull-up/pull-down |
| endpoint_off_grid | warning | Wire/pin not on 1.27mm grid | Snap all coordinates with `snap()` |
| lib_symbol_mismatch | warning | Embedded symbol differs from library | Re-copy symbol from library OR suppress in .kicad_pro (safe for KiCad 8→9 migration) |
| lib_symbol_issues | warning | Symbol not found in referenced library | Create project-level custom library with the symbol; update lib_id to point there |
| unconnected_wire_endpoint | warning | Wire end not connected to anything | Extend wire to pin/label or remove dangling wire |
| no_connect_connected | warning | No-connect flag on a pin that IS connected | Remove the no_connect flag (the pin has a real connection) |
| multiple_net_names | warning | Two labels on same net create dual names | Intentional: suppress in .kicad_pro. Accidental: remove one label |
| footprint_link_issues | warning | Footprint not found in library | Update footprint name to KiCad 9 equivalent using `replace_footprint()` |
| unannotated | error (GUI) | Reference doesn't end with digit | Use `fix_annotation_suffixes()` — note: CLI ERC doesn't catch this |

### Error Priority (Fix in This Order)

1. **Sub-symbol naming** — fixes lib_symbol_issues and lib_symbol_mismatch
2. **Grid snapping** — fixes endpoint_off_grid and prevents cascading errors
3. **Pin connectivity** — fixes pin_not_connected, label_dangling (requires correct pin positions)
4. **PWR_FLAG placement** — fixes power_pin_not_driven
5. **No-connect flags** — fixes remaining pin_not_connected on unused pins

## Debugging Tips

### Verifying Pin Positions
If you get label_dangling or pin_not_connected errors, the most likely cause is wrong pin positions. To debug:

1. Open the .kicad_sym file and find the pin definition
2. Note the library coordinates (X, Y)
3. Apply the transform formula for the component's rotation
4. Compare with the wire/label position in the .kicad_sch file
5. If they don't match exactly, the connection is broken

### Checking Wire Connectivity
A wire connects two points only if both endpoints exactly match pin/label positions. Use search to find all `(xy ...)` coordinates near a pin's expected position and verify they match.

### ERC Report Parsing
```bash
kicad-cli sch erc --output report.json --format json --severity-all schematic.kicad_sch
```

**Always use `--severity-all`** to include warnings (default only shows errors).

**Always use `-o file.json`** — kicad-cli writes JSON to the output file, NOT to stdout. Piping to python gives empty stdin.

The JSON output contains `severity`, `type`, and position information for each error. Group errors by type to identify systematic issues (e.g., all label_dangling errors suggesting a coordinate transform bug).

**KiCad 9 JSON format** nests violations under `sheets[].violations[]`:
```json
{
  "sheets": [
    {
      "path": "/",
      "uuid_path": "/root-uuid",
      "violations": [
        {
          "description": "Input Power pin not driven...",
          "severity": "error",
          "type": "power_pin_not_driven",
          "items": [...]
        }
      ]
    }
  ]
}
```

This differs from KiCad 8 which uses top-level `violations[]`. The helper `run_erc()` handles both formats.

---

## KiCad 9 Differences

### Symbol Renames

Symbols renamed or removed between KiCad 8 and 9:

| KiCad 8 | KiCad 9 | Notes |
|---|---|---|
| `Connector:Conn_01x04` | `Connector:Conn_01x04_Pin` | All Conn_01xNN renamed |
| `Connector:Conn_01x06` | `Connector:Conn_01x06_Pin` | Same pattern |
| `Connector:Conn_02x20` | `Connector:Conn_02x20_Pin` | All Conn_02xNN renamed |
| `Connector:SMA` | Removed | No direct replacement |
| `Connector:TestPoint` | `Connector:TestPoint` | May have moved/changed |
| `Regulator_Linear:AMS1117` | Has 4 pins (ADJ added) | 3-pin schematic breaks |

### Pin Position Changes

**CRITICAL — Do NOT update these symbols:**

| Symbol | KiCad 8 Pins | KiCad 9 Pins | Impact |
|---|---|---|---|
| `Device:C` | (0, ±2.54) | (0, ±3.81) | Breaks every capacitor connection |
| `Device:R` | (0, ±2.54) | (0, ±3.81) | Breaks every resistor connection |
| `Device:L` | (0, ±2.54) | (0, ±3.81) | Breaks every inductor connection |

The embedded symbols in the schematic work correctly because they contain the original pin positions. Suppress `lib_symbol_mismatch` instead of updating.

### Footprint Renames

| KiCad 8 | KiCad 9 |
|---|---|
| `Button_Switch_SMD:SW_Push_1P1T_NO_6x3.5mm` | `Button_Switch_SMD:SW_Push_1P1T_NO_CK_PTS125Sx43SMTR` |
| `Connector_Coaxial:SMA_Amphenol_901-143_Vertical` | `Connector_Coaxial:SMA_Amphenol_901-144_Vertical` |

### Annotation Requirements

KiCad 9 requires all reference designators to end with a digit. This is enforced by the GUI but NOT by CLI ERC.

Affected references (examples): `C_RX1B_N`, `C_TX2A_P`, `J_PWR`, `R_BIAS`

Fix: append `1` to each bare reference in both property and instance sections.

---

## Environment Variables for kicad-cli

On macOS, `kicad-cli` may not find the global symbol/footprint libraries without these:

```bash
export KICAD9_SYMBOL_DIR="/Applications/KiCad/KiCad.app/Contents/SharedSupport/symbols"
export KICAD9_FOOTPRINT_DIR="/Applications/KiCad/KiCad.app/Contents/SharedSupport/footprints"
```

Without these, ERC will report false `lib_symbol_issues` warnings for every symbol from global libraries.

Full ERC command:
```bash
KICAD9_SYMBOL_DIR="/Applications/KiCad/KiCad.app/Contents/SharedSupport/symbols" \
KICAD9_FOOTPRINT_DIR="/Applications/KiCad/KiCad.app/Contents/SharedSupport/footprints" \
/Applications/KiCad/KiCad.app/Contents/MacOS/kicad-cli sch erc \
  --format json --severity-all -o /tmp/erc_result.json schematic.kicad_sch
```

---

## Project Library Tables

When standard KiCad libraries change between versions, use project-level library tables to add custom symbol/footprint libraries.

### sym-lib-table (symbol library table)

Place in project root directory:
```
(sym_lib_table
  (version 7)
  (lib (name "CubeSat_SDR")(type "KiCad")(uri "${KIPRJMOD}/libraries/cubesat_sdr.kicad_sym")(options "")(descr "Project custom symbols"))
)
```

### fp-lib-table (footprint library table)

Place in project root directory:
```
(fp_lib_table
  (version 7)
  (lib (name "CubeSat_SDR")(type "KiCad")(uri "${KIPRJMOD}/libraries/cubesat_sdr.pretty")(options "")(descr "Project custom footprints"))
)
```

### Key Notes

- `${KIPRJMOD}` resolves to the project directory — use it for portable paths
- Project-level tables supplement (don't replace) global library tables
- Library names must match the prefix used in `lib_id` references (e.g., `CubeSat_SDR:AMS1117` needs a library named `CubeSat_SDR`)
- `.kicad_sym` files use the same s-expression format as embedded `lib_symbols`, but top-level symbols omit the library prefix
