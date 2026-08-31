# TinyNFC KiCad project

KiCad 7 schematic and PCB for the batteryless NFC energy-harvesting audio
player described in [`../design.md`](../design.md).

## Open the project

```bash
kicad tinynfc/kicad/tinynfc.kicad_pro
```

Requires KiCad 7 or later with the standard symbol/footprint libraries.

## What's in the design

| Ref | Part | Role |
|-----|------|------|
| U1 | NT3H2111W0FHKH | NFC harvest (`VOUT`) + antenna |
| L1 | PCB spiral | ~2.75 µH rectangular spiral on `F.Cu` |
| C1 | 1.5 pF 0402 | Antenna fine tune |
| C2 | 100 nF 0402 | Hard-tied `VOUT` bypass (<220 nF limit) |
| Q1 | DMP21D0UFB4 | P-FET gate for delayed bulk cap |
| R1 | 100 kΩ | Gate pull-up (FET off at field entry) |
| R2 | 2.2 kΩ | Gate series limit from `CAP_EN` |
| C3 | 10 µF 0402 | Gated bulk reservoir on `VBULK` |
| U2 | ATtiny816-MNR | Melody PWM + gate control |
| R3 | 220 Ω | Piezo series current limit |
| PZ1 | FUET-9018 | Passive 9×9 piezo (PKMCS0909 land) |
| D1 | TPESD8L3_3CT5G | UPDI ESD TVS |
| TP1–TP3 | 1.0 mm pads @ 2.54 mm | GND / VCC / UPDI pogo |

### MCU pin map

| Net | Pin | Function |
|-----|-----|----------|
| `UPDI` | PA0 | Programming |
| `CAP_EN` | PA7 | Drive P-FET gate low after ~120 ms |
| `PIEZO_A` | PB0 | TCA0 WO0 |
| `PIEZO_B` | PB1 | Complementary drive |

NTAG `VCC` is tied to `VOUT` (self-powered). `SCL` / `SDA` / `FD` are unused
in this revision (no-connects).

## Layout rules

- Board: **28 mm × 28 mm** postage stamp (not credit-card size). A larger
  outline couples more RF; this one is the minimum that still fits a 9 mm
  piezo in the spiral island plus UPDI pads in the edge margin.
- Antenna: 23 mm square spiral, 6 turns, 0.35 / 0.28 mm trace/gap on `F.Cu`.
  Do **not** add a continuous GND plane under it.
- Footprint reference designators are hidden on silk so they do not sit on
  copper. Only GND / VCC / UPDI pad labels are silkscreened.
- Keep the piezo + gated bulk path short inside the spiral island.

## Regenerate

```bash
python3 tinynfc/kicad/scripts/generate_project.py
```

Schematic connectivity uses net labels. After opening in KiCad, run **Update
PCB from Schematic**, then route the ratsnest. The generator places footprints
but does not auto-route.

## Status

Draft for requirements iteration. Not fabrication-ready: confirm antenna
inductance on the VNA, FET/TVS land patterns against manufacturer drawings,
and run ERC/DRC in KiCad before ordering boards.
