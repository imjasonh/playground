# Board and mechanical stack-up

## PCB

- 4 layers: signal / ground / power / signal.
- Thickness ~0.8 mm.
- Outline follows the panel, about 91 x 77 mm.
- A solid ground plane sits under the radio and the panel SPI runs. The antenna
  gets a ground keep-out and lives at the edge farthest from the magnet ring and
  the Qi coil, which both detune 2.4 GHz. Tune the matching network with a phone
  attached, not on the bench.

## Placement

- Front: the e-ink panel, adhered over the PCB.
- Back: the LiPo cell, the Qi receive coil with its ferrite shield, and the
  MagSafe magnet ring.
- The magnet ring is annular; the coil sits inside it, matching Apple's ring
  geometry so the tile self-aligns on a charger.

## Vertical stack (approximate)

| Layer | Thickness |
|-------|-----------|
| E-ink panel + FPC | 1.0 mm |
| PCB | 0.8 mm |
| LiPo cell | 2.0 mm |
| RX coil + ferrite | 0.6 mm |
| Magnet ring + skins/adhesive | 0.8 mm |
| Total (approx.) | ~4.5 mm |

The coil, cell, and magnets set the floor, so the tile is about 4.5 mm: thicker
than a MagSafe wallet, thinner than a battery pack.

## Retention

Magnet-only. The MagSafe magnet ring holds the tile to the phone and self-aligns
it on a charger; there is no adhesive skin, so the tile stays swappable between
phones and cases.

## Thermal

Receive-only charging keeps heat low. The NTC thermistor feeds both the SAADC
(for the status readout) and the charger's thermal cutoff. If pass-through were
ever added (it is not in this design), the transmit coil would need its own
thermistor and power foldback.
