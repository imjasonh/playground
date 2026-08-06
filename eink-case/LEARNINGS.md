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

No bezel↔tray screw joint. Cap uses snaps and/or a couple of M2 pilots into
the shell’s open-end bosses.

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
