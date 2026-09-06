#!/usr/bin/env python3
"""Generate a thickness-first PCB outline for inkbot-magsafe (KiCad 7 format).

No case: the 4.2\" panel is the front face. The LiPo sits in a board cutout so
its thickness does not stack on the 0.4 mm PCB. MagSafe magnets and the Qi coil
share the back plane. Footprints are placed afterward with place_footprints.py.
"""

from __future__ import annotations

import uuid
from pathlib import Path

OUT = Path(__file__).resolve().parent / "inkbot-magsafe.kicad_pcb"

BOARD_W = 91.0
BOARD_H = 77.0
RING_DIA = 54.9
COIL_DIA = 40.0
BAT_W, BAT_H = 32.0, 22.0


def uid() -> str:
    return str(uuid.uuid4())


def rect_outline(x0: float, y0: float, w: float, h: float, layer: str, width: float = 0.1) -> str:
    x1, y1 = x0 + w, y0 + h
    pts = [(x0, y0), (x1, y0), (x1, y1), (x0, y1), (x0, y0)]
    lines = []
    for (ax, ay), (bx, by) in zip(pts, pts[1:]):
        lines.append(
            f'  (gr_line (start {ax:.3f} {ay:.3f}) (end {bx:.3f} {by:.3f})\n'
            f'    (stroke (width {width}) (type solid)) (layer "{layer}") (tstamp {uid()}))'
        )
    return "\n".join(lines)


def circle(cx: float, cy: float, r: float, layer: str, width: float = 0.1) -> str:
    return (
        f'  (gr_circle (center {cx:.3f} {cy:.3f}) (end {cx + r:.3f} {cy:.3f})\n'
        f'    (stroke (width {width}) (type solid)) (fill none) (layer "{layer}") (tstamp {uid()}))'
    )


def text(s: str, x: float, y: float, layer: str, size: float = 1.0) -> str:
    return (
        f'  (gr_text "{s}" (at {x:.3f} {y:.3f} 0)\n'
        f'    (layer "{layer}") (tstamp {uid()})\n'
        f'    (effects (font (size {size} {size}) (thickness 0.15))))'
    )


def main() -> None:
    cx, cy = BOARD_W / 2, BOARD_H / 2
    bat_x = cx - BAT_W / 2
    bat_y = cy - BAT_H / 2

    graphics = [
        rect_outline(0, 0, BOARD_W, BOARD_H, "Edge.Cuts", 0.05),
        rect_outline(bat_x, bat_y, BAT_W, BAT_H, "Edge.Cuts", 0.05),
        circle(cx, cy, RING_DIA / 2, "Dwgs.User", 0.15),
        circle(cx, cy, COIL_DIA / 2, "Dwgs.User", 0.1),
        text("MagSafe ring PCD", cx, cy - RING_DIA / 2 - 1.5, "Dwgs.User", 0.8),
        text("Qi coil keep-in", cx, cy + COIL_DIA / 2 + 1.5, "Dwgs.User", 0.8),
        text("LiPo cutout", cx, bat_y - 1.5, "Dwgs.User", 0.8),
        text("inkbot-magsafe 0.4mm 4-layer  no case", 2, 2, "Cmts.User", 1.0),
    ]

    pcb = f"""(kicad_pcb (version 20221018) (generator pcbnew)

  (general
    (thickness 0.4)
  )

  (paper "A4")
  (title_block
    (title "inkbot-magsafe")
    (date "2026-09-06")
    (rev "0.2.0")
    (comment 1 "0.4 mm 4-layer; battery cutout; no case — panel is the front face")
    (comment 2 "Place magnets + Qi coil on back; keep antenna outside magnet ring")
  )

  (layers
    (0 "F.Cu" signal)
    (1 "In1.Cu" signal)
    (2 "In2.Cu" signal)
    (31 "B.Cu" signal)
    (32 "B.Adhes" user "B.Adhesive")
    (33 "F.Adhes" user "F.Adhesive")
    (34 "B.Paste" user)
    (35 "F.Paste" user)
    (36 "B.SilkS" user "B.Silkscreen")
    (37 "F.SilkS" user "F.Silkscreen")
    (38 "B.Mask" user)
    (39 "F.Mask" user)
    (40 "Dwgs.User" user "User.Drawings")
    (41 "Cmts.User" user "User.Comments")
    (44 "Edge.Cuts" user)
    (46 "B.CrtYd" user "B.Courtyard")
    (47 "F.CrtYd" user "F.Courtyard")
    (48 "B.Fab" user)
    (49 "F.Fab" user)
  )

  (setup
    (pad_to_mask_clearance 0)
    (stackup
      (layer "F.SilkS" (type "Top Silk Screen"))
      (layer "F.Paste" (type "Top Solder Paste"))
      (layer "F.Mask" (type "Top Solder Mask") (thickness 0.01))
      (layer "F.Cu" (type "copper") (thickness 0.018))
      (layer "dielectric 1" (type "prepreg") (thickness 0.07) (material "FR4") (epsilon_r 4.5) (loss_tangent 0.02))
      (layer "In1.Cu" (type "copper") (thickness 0.018))
      (layer "dielectric 2" (type "core") (thickness 0.15) (material "FR4") (epsilon_r 4.5) (loss_tangent 0.02))
      (layer "In2.Cu" (type "copper") (thickness 0.018))
      (layer "dielectric 3" (type "prepreg") (thickness 0.07) (material "FR4") (epsilon_r 4.5) (loss_tangent 0.02))
      (layer "B.Cu" (type "copper") (thickness 0.018))
      (layer "B.Mask" (type "Bottom Solder Mask") (thickness 0.01))
      (layer "B.Paste" (type "Bottom Solder Paste"))
      (layer "B.SilkS" (type "Bottom Silk Screen"))
      (copper_finish "None")
      (dielectric_constraints no)
    )
    (pcbplotparams
      (layerselection 0x00010fc_ffffffff)
      (plot_on_all_layers_selection 0x0000000_00000000)
      (disableapertmacros false)
      (usegerberextensions false)
      (usegerberattributes true)
      (usegerberadvancedattributes true)
      (creategerberjobfile true)
      (dashed_line_dash_ratio 12.000000)
      (dashed_line_gap_ratio 3.000000)
      (svgprecision 4)
      (plotframeref false)
      (viasonmask false)
      (mode 1)
      (useauxorigin false)
      (hpglpennumber 1)
      (hpglpenspeed 20)
      (hpglpendiameter 15.000000)
      (dxfpolygonmode true)
      (dxfimperialunits true)
      (dxfusepcbnewfont true)
      (psnegative false)
      (psa4output false)
      (plotreference true)
      (plotvalue true)
      (plotinvisibletext false)
      (sketchpadsonfab false)
      (subtractmaskfromsilk false)
      (outputformat 1)
      (mirror false)
      (drillshape 1)
      (scaleselection 1)
      (outputdirectory "")
    )
  )

  (net 0 "")

{chr(10).join(graphics)}

)
"""
    OUT.write_text(pcb)
    print(f"wrote {OUT} ({OUT.stat().st_size} bytes)")
    print(f"board {BOARD_W}x{BOARD_H} mm, thickness 0.4 mm, battery cutout {BAT_W}x{BAT_H} mm")


if __name__ == "__main__":
    main()
