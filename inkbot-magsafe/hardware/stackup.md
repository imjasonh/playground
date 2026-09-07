# Board and mechanical stack-up

## PCB

- 4 layers: signal / ground / power / signal.
- Thickness **0.4 mm** (thin FR4; confirm fab yield before volume).
- Outline **60 × 99 mm, portrait** — fits a 6.1" Pro (70.6 × 146.6 mm) in both
  width and height with the MagSafe ring high. Minis (64.2 mm) are out of scope;
  the 4.26" panel (105 mm tall) overshoots the bottom of a 15 Pro and was dropped.
- **Battery cutout** (~32 × 20 mm) below the coil so the LiPo thickness does not
  stack on the PCB.
- Solid ground under the radio and panel SPI. Antenna keep-out at the **bottom**
  edge, farthest from the ring and coil. Tune matching with a phone attached.

## No case

The 3.97-inch panel is the front face (adhesive bond to the PCB) and covers the
whole board. The back holds the Qi coil, ferrite, MagSafe magnet ring, and the
components. There is no plastic shell for the first spin.

## Placement

- Front: 3.97-inch e-ink panel (480 × 800), FPC into the connector. The panel
  **overlaps the MagSafe ring** — coil and magnets are behind it on the back.
- Back, top: Qi RX coil inside the MagSafe magnet ring, ring center **30 mm from
  the top edge** (Apple's keep-in limit toward the phone top).
- Back, below the coil: nRF52833, BQ51050B, load switch, LDO, passives ringing
  the cutout.
- Cutout: thin ~120 mAh LiPo (~1.5 mm).

## Camera and bottom clearance

Apple's Accessory Design Guidelines cap a MagSafe accessory at **30 mm from the
ring center toward the phone's top edge**. Putting the ring that high on the
tile and hanging the body downward keeps the whole tile below the rear-camera
plateau. On a 15 Pro that leaves ~104 mm of vertical room; the 99 mm board sits
inside it with ~4 mm above the phone's bottom edge.

## Vertical stack (thickest region)

With the cell in the cutout, the PCB does not sit under the cell:

| Layer | Thickness |
|-------|-----------|
| E-ink panel + adhesive | ~1.05 mm |
| LiPo in cutout | ~1.5 mm |
| **Total at cell** | **~2.55 mm** |

Around the magnet ring (no cell, back-mounted parts + coil):

| Layer | Thickness |
|-------|-----------|
| Panel + adhesive | ~1.05 mm |
| PCB | 0.4 mm |
| Coil + ferrite / parts | ~0.5–0.6 mm |
| **Total at ring** | **~2.0–2.1 mm** |

## Retention

Magnet-only. The MagSafe ring holds the tile to the phone and self-aligns it on
a charger.
