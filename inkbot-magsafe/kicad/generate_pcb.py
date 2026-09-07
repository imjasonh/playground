#!/usr/bin/env python3
"""Generate the EVT PCB outline and mechanical reference layers.

The 3.97-inch panel covers the front. The receiver coil, magnetic array,
protected cell, electronics, structural spacer, and protective back film sit
behind it. The ring center is 30 mm from the top edge for camera clearance.
"""

from __future__ import annotations

import uuid
from pathlib import Path

OUT = Path(__file__).resolve().parent / "inkbot-magsafe.kicad_pcb"

# Portrait outline. 3.97" module is 56.24 x 96.62 mm; a 60 x 99 mm board clears
# the panel and fits a 6.1" Pro in BOTH width (70.6 mm) and height (~104 mm
# available below the camera keep-in). The 4.26" (105 mm tall) overshoots the
# bottom of a 15 Pro; minis (64.2 mm) are still dropped for width.
BOARD_W = 60.0
BOARD_H = 99.0

# The public drawing is an EVT reference. MFi mechanical data and measured
# pull-force results control the production magnetic array.
RING_CY = 30.0
RING_OD = 54.0
RING_ID = 46.0
COIL_SHIELD_DIA = 22.0

# Panel module outline (front face), near the top so it overlaps the ring.
PANEL_W, PANEL_H = 56.24, 96.62
PANEL_TOP = 1.2

# LP252030 pack envelope after its protection circuit, plus 1 mm clearance.
BAT_W, BAT_H = 33.0, 22.0
BAT_CY = 70.0


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
    cx = BOARD_W / 2
    bat_x = cx - BAT_W / 2
    bat_y = BAT_CY - BAT_H / 2
    panel_x = cx - PANEL_W / 2

    graphics = [
        rect_outline(0, 0, BOARD_W, BOARD_H, "Edge.Cuts", 0.05),
        rect_outline(bat_x, bat_y, BAT_W, BAT_H, "Edge.Cuts", 0.05),
        # Panel outline (front face) on the fab layer.
        rect_outline(panel_x, PANEL_TOP, PANEL_W, PANEL_H, "Cmts.User", 0.1),
        circle(cx, RING_CY, RING_OD / 2, "Dwgs.User", 0.15),
        circle(cx, RING_CY, RING_ID / 2, "Dwgs.User", 0.15),
        circle(cx, RING_CY, COIL_SHIELD_DIA / 2, "Dwgs.User", 0.1),
        text("54 x 46 mm EVT magnetic array", cx, RING_CY, "Dwgs.User", 0.65),
        text(
            "WR222230 coil shield",
            cx,
            RING_CY + COIL_SHIELD_DIA / 2 + 1.5,
            "Dwgs.User",
            0.65,
        ),
        text("LP252030 protected-cell cutout", cx, bat_y - 1.5, "Dwgs.User", 0.7),
        text("GDEM0397T81P panel outline", cx, BOARD_H - 2, "Cmts.User", 0.7),
        text(
            "EVT geometry; production magnet data requires MFi approval",
            2,
            2,
            "Cmts.User",
            0.7,
        ),
    ]

    pcb = f"""(kicad_pcb (version 20221018) (generator pcbnew)

  (general
    (thickness 0.8)
  )

  (paper "A4")
  (title_block
    (title "inkbot-magsafe")
    (date "2026-09-07")
    (rev "0.6.0")
    (comment 1 "0.8 mm four-layer EVT board; protected-cell cutout; structural spacer and protective films")
    (comment 2 "BQ51013C + BQ25185; Raytac MDBT50Q-512K; GDEM0397T81P")
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
      (layer "dielectric 1" (type "prepreg") (thickness 0.075) (material "FR4") (epsilon_r 4.5) (loss_tangent 0.02))
      (layer "In1.Cu" (type "copper") (thickness 0.018))
      (layer "dielectric 2" (type "core") (thickness 0.55) (material "FR4") (epsilon_r 4.5) (loss_tangent 0.02))
      (layer "In2.Cu" (type "copper") (thickness 0.018))
      (layer "dielectric 3" (type "prepreg") (thickness 0.075) (material "FR4") (epsilon_r 4.5) (loss_tangent 0.02))
      (layer "B.Cu" (type "copper") (thickness 0.018))
      (layer "B.Mask" (type "Bottom Solder Mask") (thickness 0.01))
      (layer "B.Paste" (type "Bottom Solder Paste"))
      (layer "B.SilkS" (type "Bottom Silk Screen"))
      (copper_finish "ENIG")
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
    print(
        f"board {BOARD_W}x{BOARD_H} mm portrait, 0.8 mm EVT, ring center {RING_CY} mm "
        f"from top, battery cutout {BAT_W}x{BAT_H} mm"
    )


if __name__ == "__main__":
    main()
