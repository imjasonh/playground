# eink-case — design learnings

Lessons from the first 3-piece sandwich (bezel + tray + back) and the
redesign to a print-upward slide-in slot.

## What failed (and why)

1. **One-piece front with a solid deck behind the glass**
   Printed bezel-down, that deck is a ~160×100 mm mid-air bridge over the
   active-area window. Fails FDM R1.2. “Add support” is not an answer for a
   cosmetic window face.

2. **Splitting into bezel + tray to put the deck on the bed**
   Printable, but assembly-heavy: four screws bezel↔tray, four more lid↔tray,
   and the panel is only trapped once the tray is on (can fall out of the
   bezel alone). Crush ribs help XY; they are not a lock.

3. **External / mid-floor ribbon holes**
   Easy to misread as “cable exits the case.” The ribbon only needs an
   *internal* path from the panel plane into the board bay. Prefer a
   backer pass into the bay at the FPC end — never a hole through the outer
   shell.

4. **Screws through the glass footprint**
   Corner bosses must sit in a rim *outside* the panel outline, or the
   fasteners hit the panel.

5. **ASCII STLs in git**
   Tens of thousands of facet lines drown the PR diff. Use binary STL
   (`--export-format=binstl`) and `*.stl binary` in `.gitattributes`.

6. **Board cradle as a shelf off the backer**
   In the print-upward orientation the backer is a vertical wall. A cradle
   that grows “up” from that face in assembly Z is a horizontal shelf in the
   print. Use rails/stops that stay vertical walls (constant X or Y), plus
   tiny beads — not a deck.

7. **Floating cradle rails / short standoff beads**
   Rails that start above `z_bay0` are disconnected solids inside the bay.
   Fuse rails to the backer (`rail_z0 = z_bay0`). Bead height must equal
   `board_standoff` / `board_z0` or the PCB floats. Leave the USB-end rail
   off so the connector can reach the wall.

8. **USB tip recessed behind the wall**
   Placing the board at `wall + margin + usb_protrude` left the connector
   ~6 mm inside. Seat with `board_x0 = usb_face + usb_protrude` (tip at
   `usb_face`, default flush) and cut PCB-edge relief through the wall
   thickness where it overlaps.

9. **PLA cantilever clips**
   The four short cap clips did not latch reliably in a real PLA print.
   Increasing flex would make layer orientation, PLA brand, and fatigue part
   of the fit contract. Replace flex retention with two rigid printed keys:
   cap and shell holes align, and the keys carry load in shear.

10. **A board path that requires a sideways move**
    A board inserted from the shell mouth could not comfortably descend and
    then move sideways into a wall USB opening. Rotate it 90°: two straight
    grooves now point at the mouth, the ZIF end enters first, and USB exits
    through the removable cap. The cap is also the board’s withdrawal stop.

11. **Nominal clearance is not long-slide clearance**
    The first full-size panel entered but accumulated enough drag to stop
    before the closed end. Increase `panel_clear` from 0.30 to 0.40 mm and
    reduce rib intrusion from 0.20 to 0.15 mm. Board rail clearance increases
    from 0.50 to 0.75 mm; neither fit relies on friction for retention.

## What worked

1. **Orientation is a design input (R1.3)** — pick the bed face first; export
   STLs already flipped. Raycast bed→up before every export.
2. **Parametric fit knobs** — `panel_clear`, `panel_crush`, chamfers; datasheet
   outline is nominal (±0.2 mm typical). Measure the real panel before a
   final print.
3. **Elephant-foot chamfers on bed faces** — small 45° relief
   (`elephant_chamfer`) plus slicer compensation.
4. **Vendored OpenSCAD skill** — validate → multi-preview → read PNGs →
   export. Never skip visual checks.

## Principle for the current design

**Print the panel groove as a U-channel extruded in Z (slide direction).**

Each layer is the U cross-section (front lip | slot | backer | bay). Nothing
spans mid-air over the window: the backer is a *vertical wall* in the print,
not a ceiling. The closed end (opposite the FPC) sits on the bed; the FPC
end is open at the top so the panel slides in after printing.

That restores a true snug slide-in slot without a 3-way screw sandwich.

## Parting line

| Part | Role |
|------|------|
| `shell` | Window, U-slot, panel backer, electronics bay, board cradle |
| `cap` | Closes the open (FPC) end; retains the panel; optional lid posts |

No bezel↔tray screw joint. Cap retention uses **two rigid printed side keys**.
Nothing bends, so PLA is appropriate; no screw heads project from the standing
end. Pull both keys to service the board or panel.

## Open mouth vs “showing innards”

The shell’s FPC end **must** stay open in the part itself — that is the
slide-in mouth (panel tunnel + bay access for board install). In print
orientation that is the top of `shell.stl`, so a lone shell preview will
show the bay. That is not a finished exterior.

What must *not* be open is the **front face** through the fold-bay strip:
keep the front lip solid there (panel tunnels *behind* it). Then the cap
closes the mouth with a full end plate, perimeter rabbet, front/back skirts,
bay plug, and a notched retention tongue. Assembled, no see-through to the
PCB from the display face or the FPC end.
