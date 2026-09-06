# Board and mechanical stack-up

## PCB

- 4 layers: signal / ground / power / signal.
- Thickness **0.4 mm** (thin FR4; confirm fab yield before volume).
- Outline follows the panel: 91 x 77 mm.
- Central **battery cutout** (~32 x 22 mm) so the LiPo thickness does not stack on
  the PCB.
- Solid ground under the radio and panel SPI. Antenna keep-out at the edge
  farthest from the MagSafe ring and Qi coil. Tune matching with a phone
  attached.

## No case

The panel is the front face (adhesive bond to the PCB). The back is the Qi coil,
ferrite, and MagSafe magnet ring. There is no plastic shell for the first
spin; add a thin PET or painted mask later only if handling needs it.

## Placement

- Front: e-ink panel + FPC into the board-edge connector.
- PCB: nRF52832 QFN, BQ51050B, load switch, LDO, passives around the cutout.
- Cutout: thin 100 mAh LiPo (~1.5 mm).
- Back (coplanar): Qi RX coil inside the MagSafe magnet ring.

## Vertical stack (thickest region)

With the cell in the cutout, the PCB does not sit under the cell:

| Layer | Thickness |
|-------|-----------|
| E-ink panel + adhesive | ~1.05 mm |
| LiPo in cutout | ~1.5 mm |
| **Total at cell** | **~2.55 mm** |

Around the magnet ring (no cell):

| Layer | Thickness |
|-------|-----------|
| Panel + adhesive | ~1.05 mm |
| PCB | 0.4 mm |
| Coil + ferrite (or magnets) | ~0.5–0.6 mm |
| **Total at ring** | **~2.0–2.1 mm** |

Earlier ~4.5 mm estimate assumed a 0.8 mm PCB and a cell stacked under the board.
This cutout + thin PCB design targets about **2.5–2.8 mm**.

## Retention

Magnet-only. The MagSafe ring holds the tile to the phone and self-aligns it on
a charger.
