# Board and mechanical stack-up

## PCB

- 4 layers: signal / ground / power / signal.
- Thickness **0.4 mm** (thin FR4; confirm fab yield before volume).
- Outline **57 × 96 mm, portrait** — narrower than every MagSafe iPhone (down to
  the 64.2 mm minis), so it fits the phone width with no side overhang.
- **Battery cutout** (~30 × 20 mm) below the coil so the LiPo thickness does not
  stack on the PCB.
- Solid ground under the radio and panel SPI. Antenna keep-out at the **bottom**
  edge, farthest from the ring and coil. Tune matching with a phone attached.

## No case

The 3.7-inch panel is the front face (adhesive bond to the PCB) and covers the
whole board. The back holds the Qi coil, ferrite, MagSafe magnet ring, and the
components. There is no plastic shell for the first spin.

## Placement

- Front: 3.7-inch e-ink panel (240 × 416), FPC into the connector. The panel
  **overlaps the MagSafe ring** — coil and magnets are behind it on the back.
- Back, top: Qi RX coil inside the MagSafe magnet ring, ring center **30 mm from
  the top edge** (Apple's keep-in limit toward the phone top).
- Back, below the coil: nRF52832, BQ51050B, load switch, LDO, passives ringing
  the cutout.
- Cutout: thin ~90 mAh LiPo (~1.5 mm).

## Camera clearance

Apple's Accessory Design Guidelines cap a MagSafe accessory at **30 mm from the
ring center toward the phone's top edge**. Putting the ring that high on the
tile and hanging the body downward keeps the whole tile below the rear-camera
plateau on every supported iPhone.

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
