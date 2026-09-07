# Board and mechanical stack-up

## PCB

- Four layers: F.Cu signal and ground pour, In1.Cu SYS plane, In2.Cu solid
  ground, and B.Cu signal and ground pour.
- The 0.8 mm prototype uses the JLC7628 four-layer stack: 35 um outer copper,
  15.2 um inner copper, 0.2104 mm 7628 prepreg, and a 0.2 mm core. Confirm the
  production order's stack table against the KiCad file before release.
- The outline is **60 x 99 mm, portrait**. The GDEM0397T81P glass is
  56.24 x 96.62 mm.
- The battery cutout is **34 x 23 mm** with 1 mm corner radii. It accepts a
  protected LP252030 pack no larger than 31 x 20 mm in plan view and leaves
  room for an adhesive carrier.
- Copper stays at least 0.5 mm from routed edges. Standard vias are 0.6 mm
  with a 0.3 mm drill, which provides a 0.15 mm nominal annular ring.
- The Raytac module's antenna end is flush with the left board edge. A
  4.8 x 12 mm keep-out removes copper, tracks, and vias from every layer.
- Surface ground pours use thermal connections for reflow consistency. The
  two inner power planes use solid connections.

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

The enclosure drawing must define adhesive width, material flammability,
water and sweat exposure, venting, drop protection, torsion, and cell swelling
allowance before a production release.

## Placement

- Front: 3.97-inch e-ink panel (480 × 800), FPC into the connector. The panel
  overlaps the magnetic ring. The coil and magnets are behind it.
- Back, top: Qi RX coil inside the MagSafe magnet ring, ring center **30 mm from
  the top edge** (Apple's keep-in limit toward the phone top).
- Back, below the coil: MDBT50Q-512K module (antenna end toward a board edge),
  BQ51013C receiver, BQ25185 charger, panel LDO, and passives around the cutout.
- Cutout: protected LP252030 100 mAh pack with an NTC and keyed harness.
- Magnetic assembly: N48H accessory ring and a low-carbon-steel DC shield.
  An orientation magnet is optional because the tile's center of mass hangs
  below the ring. If testing shows unacceptable rotation, add the orientation
  magnet and requalify Qi coupling, pull force, and the thickness stack.

## Camera and bottom clearance

Apple's Accessory Design Guidelines cap a MagSafe accessory at **30 mm from the
ring center toward the phone's top edge**. Putting the ring that high on the
tile and hanging the body downward keeps the whole tile below the rear-camera
plateau. On a 15 Pro that leaves ~104 mm of vertical room; the 99 mm board sits
inside it with ~4 mm above the phone's bottom edge.

## Vertical stack

The following budgets include 0.10 mm front adhesive and a 0.25 mm rear cover.
They do not include tolerance compression, cosmetic film, or an optional
orientation magnet.

| Layer | Thickness |
|-------|-----------|
| E-ink panel + adhesive | ~1.02 mm |
| PCB | 0.8 mm |
| MDBT50Q-512K module | ~2.0 mm |
| Rear cover | ~0.25 mm |
| **Total at module** | **~4.07 mm** |

At the cell (cutout, so the PCB does not sit under the cell):

| Layer | Thickness |
|-------|-----------|
| E-ink panel + adhesive | ~1.02 mm |
| Protected LP252030 pack | up to 3.2 mm |
| Rear cover | ~0.25 mm |
| **Total at cell** | **~4.47 mm** |

At the magnetic ring:

| Layer | Thickness |
|-------|-----------|
| Panel + adhesive | ~1.02 mm |
| PCB | 0.8 mm |
| Accessory magnet array and DC shield | ~1.2 mm |
| Rear cover | ~0.25 mm |
| **Total at ring** | **~3.27 mm** |

At the coil center, the 0.87 mm coil and ferrite replace the annular magnet
stack, for an approximate total of 2.94 mm.

## Retention

Magnet-only. The accessory ring must meet Apple's published polarity, flux,
coplanarity, and 650-900 gf pull-force requirements. Validate pull force on
every supported phone and case, then repeat the test after drop, thermal-cycle,
and adhesive-aging tests.
