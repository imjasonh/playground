# Board and mechanical stack-up

## PCB

- Four layers: F.Cu signal, In1.Cu SYS plane, In2.Cu solid ground, and B.Cu
  signal.
- The 0.8 mm prototype uses the JLC7628 four-layer stack: 35 um outer copper,
  15.2 um inner copper, 0.2104 mm 7628 prepreg, and a 0.2 mm core. Confirm the
  production order's stack table against the KiCad file before release.
- The outline is **60 x 99 mm, portrait**. The GDEY0397T81P glass is
  56.24 x 96.62 mm.
- The battery cutout is **34 x 23 mm** with 1 mm corner radii. It accepts a
  protected LP242030 pack no larger than 31 x 20.5 mm in plan view and leaves
  room for an adhesive carrier.
- Copper stays at least 0.5 mm from routed edges. Signal clearance is 0.12 mm.
  Standard vias are 0.5 mm with a 0.25 mm drill, which provides a 0.125 mm
  nominal annular ring. Both values remain within the selected fabricator's
  standard multilayer capability.
- The Raytac module's antenna end is flush with the left board edge. The
  footprint and board rule remove copper, tracks, and vias from every layer
  under the antenna without covering the module's ground lands. Raytac must
  approve the final host layout.
- Every ground pad reaches In2.Cu through an explicit via. This avoids
  disconnected surface-pour islands and gives the signal layers an unbroken
  inner return reference.
- The panel rails reach 40 V peak-to-peak. Keep their external copper under
  intact solder mask, do not expose them on test pads, and cover the assembled
  circuit with the specified electrical insulation.
- Five adjacent bottom-edge pogo pads expose SWDIO, SWDCLK, reset, MCU_3V0, and
  ground. Three component-side fiducials support assembly alignment.

## Laminated enclosure

The glass panel is the front face, but production units cannot leave the cell,
coil joints, or panel high-voltage circuit exposed. The assembly needs:

- A pressure-sensitive adhesive frame that supports the panel outside its
  active area without loading the glass.
- A rigid, flame-retardant spacer around the cell and back-side components.
- A thin rear cover with electrical insulation over the coil terminals and
  panel circuit.
- Strain relief for the panel FPC, battery harness, and both coil leads.
- A removable fixture cover or labeled access area for the SWD pads.
- For an EU launch, reusable rear access that lets a service technician replace
  the keyed battery pack with commercially available tools, without heat,
  solvent, or removing the display.

The enclosure drawing must define adhesive width, material flammability,
water and sweat exposure, venting, drop protection, torsion, and cell swelling
allowance before a production release.

## Placement

- Front: 3.97-inch e-ink panel (480 × 800), FPC into the connector. The panel
  overlaps the magnetic ring. The coil and magnets are behind it.
- Back, top: Qi RX coil inside the MagSafe magnet ring, ring center **30 mm from
  the top edge** as an EVT fit hypothesis.
- Back, below the coil: MDBT50Q-1MV2 module (antenna end toward a board edge),
  BQ51013C receiver, BQ25186 charger, MCU and panel LDOs, and passives around
  the cutout.
- Cutout: protected LP242030 100 mAh custom pack with an NTC, keyed harness,
  and at least 200 mA continuous pack-level discharge capability.
- Magnetic assembly: N48H accessory ring and a low-carbon-steel DC shield.
  The 60 x 99 mm body extends outside the all-orientation envelope, so a
  qualified anti-rotation feature is mandatory. The current center orientation
  magnet sketch overlaps the battery cutout and is not a releasable solution.
  Freeze a safe geometry before DVT and requalify Qi coupling, pull force, and
  the thickness stack.

## Camera and bottom clearance

The 30 mm ring-center offset is an EVT placement hypothesis, not a generic
MagSafe camera-clearance rule. Before claiming phone compatibility, overlay the
complete assembly on Apple's dimensional drawing for every supported model and
include camera keep-outs, phone curvature, case lips, rotation, lateral slip,
and all manufacturing tolerances. Confirm the result on physical phones.

## Vertical stack

The following budgets include 0.10 mm front adhesive and a 0.25 mm rear cover.
They do not include tolerance compression, cosmetic film, or an optional
orientation magnet.

| Layer | Thickness |
|-------|-----------|
| E-ink panel + adhesive | ~1.02 mm |
| PCB | 0.8 mm |
| MDBT50Q-1MV2 module | ~2.05 mm |
| Rear cover | ~0.25 mm |
| **Total at module** | **~4.12 mm** |

At the cell (cutout, so the PCB does not sit under the cell):

| Layer | Thickness |
|-------|-----------|
| E-ink panel + adhesive | ~1.02 mm |
| Protected LP242030 pack | up to 3.5 mm |
| Rear cover | ~0.25 mm |
| **Total at cell** | **~4.77 mm** |

At the magnetic ring:

| Layer | Thickness |
|-------|-----------|
| Panel + adhesive | ~1.02 mm |
| PCB | 0.8 mm |
| Accessory magnet array and DC shield | ~1.2 mm |
| Rear cover | ~0.25 mm |
| **Total at ring** | **~3.27 mm** |

At the coil center, the 0.87 mm coil and ferrite replace the annular magnet
stack. The 0.5 mm film thermistor brings the conservative stacked total to
3.44 mm unless the released carrier provides a sensor pocket.

## Retention

Magnet-only. The accessory ring must meet the current Apple program's polarity,
flux, coplanarity, and force procedures. Use 650-900 gf only as the project's
provisional internal removal-force target until Apple approves the released
geometry. Validate pull force on every supported phone and case, then repeat
the test after drop, thermal-cycle, and adhesive-aging tests.
