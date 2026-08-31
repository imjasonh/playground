# TinyNFC

Batteryless NFC energy-harvesting audio player: tap a phone, harvest RF, play a
short chiptune on a piezo. No battery.

The harvest / delayed-bulk / ATtiny816 architecture follows Wilson Harper's
[NFC energy-harvesting PCB business card](https://wilsonharper.net/projects/businesscard/)
(LEDs on a full-size card). This project swaps the LEDs for a piezo and aims for
a postage-stamp outline instead.

## Docs

| File | What |
|------|------|
| [`design.md`](design.md) | Requirements, architecture, layout rules |
| [`BOM.md`](BOM.md) | Parts, supplier links, cost at 10 / 50 / 100 |
| [`kicad/`](kicad/) | KiCad 7 schematic + PCB (see [`kicad/README.md`](kicad/README.md)) |

## Quick facts

- Board: **28 mm × 28 mm × 1.6 mm** FR-4 (~**3.4 mm** assembled with the piezo)
- Harvest: NXP `NT3H2111` + PCB spiral antenna
- MCU: ATtiny816, differential PWM into a 9×9 SMD piezo
- Program once over UPDI pogo pads

Regenerate the KiCad project:

```bash
python3 tinynfc/kicad/scripts/generate_project.py
```
