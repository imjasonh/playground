# TinyNFC design

A batteryless, low-profile PCB powered only by a smartphone NFC reader's RF
field. Harvested energy runs a tiny AVR that synthesizes monophonic,
chiptune-style audio through a passive surface-mount piezo transducer.

This document is the working requirements and architecture sketch. Expect it to
change as parts, layout, and firmware constraints get validated on the bench.

## Goal

Hold a phone near the board. The board powers on from the NFC field, plays a
short melody, then sleeps until the phone is removed and brought back.

No battery. No coin cell. No USB power in the field. Programming happens once
over UPDI pads at the bench.

## Hardware architecture

### Energy harvesting and RF

| Part | Role |
|------|------|
| NXP NTAG I2C Plus (`NT3H2111W0FHKH`) | Harvests 13.56 MHz RF energy; supplies roughly 5–15 mA at 2–3 V on `VOUT` |
| PCB antenna | Rectangular spiral trace tuned to about 2.75 µH so it resonates at 13.56 MHz with the NXP chip's internal 50 pF capacitor |
| 1.5 pF tuning capacitor (0402) | Fine-tunes antenna resonance |

The NTAG is the power source for the rest of the board. Treat its `VOUT`
current and voltage as a hard budget, not a soft target.

### Microcontroller

| Candidate | Package notes | Memory |
|-----------|---------------|--------|
| Microchip ATtiny816 (`ATTINY816-MNR`) | QFN, preferred for low profile | 8 KB Flash |
| ATtiny412 | Smaller alternative if pin and Flash budget fit | Check Flash against melody size |

Eight kilobytes of Flash is enough for on the order of 1,500 notes when each
note is four bytes (`uint16_t` frequency + `uint16_t` duration).

Underclock the MCU (for example to 1 MHz) so idle draw stays low and most of
the harvested current stays available for the piezo.

### Audio output

| Part | Role |
|------|------|
| Passive SMD piezo (for example Murata `PKLCS1212E4001-R1`) | Acoustic output |
| Hardware PWM on the MCU | Square-wave drive at the note frequency |
| Series resistor (100–330 Ω) | Limits piezo switching transients so they stay inside the NFC power budget |

Wire the piezo across two GPIO pins for differential drive when you need more
volume. That doubles the voltage swing across the element compared with
single-ended drive to ground.

### Power management

NXP restricts capacitance directly on `VOUT` to less than 220 nF. A larger
capacitor on `VOUT` at field entry causes inrush that collapses the rail and
can leave the MCU in a boot loop.

**Delayed smoothing circuit**

1. Keep a 10 µF capacitor (0402) disconnected from `VOUT` at field entry.
2. A P-channel MOSFET (`DMP21D0UFB4-P`) gates that capacitor.
3. An RC timer (100 kΩ pull-up, 2.2 kΩ limit resistor) holds the MOSFET gate
   high for about the first 120 ms after RF power appears, so the big
   capacitor stays off during the fragile cold-start window.
4. After that delay, the MCU pulls the gate low, connecting the 10 µF
   capacitor and giving a low-impedance reservoir for piezo switching dips.

Until the MCU asserts the gate, treat the rail as thin. Don't start PWM until
the MOSFET is on.

### Programming interface

Three exposed pads at 2.54 mm pitch for a temporary pogo-pin clip:

| Pad | Signal |
|-----|--------|
| 1 | `GND` |
| 2 | `VCC` |
| 3 | `UPDI` |

Bridge `UPDI` to `GND` with a TVS diode (`TPESD8L3_3CT5G`) for ESD protection
on the programming line.

## Bill of materials (draft)

Priced supplier links and a 100-board cost roll-up are in [`BOM.md`](BOM.md).

| Ref / function | Part / value | Package / notes |
|----------------|--------------|-----------------|
| NFC / energy harvest | NXP `NT3H2111W0FHKH` | NTAG I2C Plus |
| Antenna | PCB spiral ≈ 2.75 µH | Tuned with chip C + external C |
| Antenna tune | 1.5 pF | 0402 |
| MCU | `ATTINY816-MNR` (or ATtiny412) | QFN preferred |
| Piezo | Murata `PKLCS1212E4001-R1` (or equivalent) | Passive SMD |
| Piezo series R | 100–330 Ω | Limit switching current |
| Bulk C (gated) | 10 µF | 0402; not hard-tied to `VOUT` |
| Gate MOSFET | `DMP21D0UFB4-P` | P-channel |
| Gate RC | 100 kΩ pull-up, 2.2 kΩ limit | ≈ 120 ms delay before MCU can connect bulk C |
| `VOUT` local C | Keep under 220 nF total hard-tied | Datasheet inrush limit |
| UPDI ESD | `TPESD8L3_3CT5G` | Across UPDI–GND |
| Program pads | GND, VCC, UPDI | 2.54 mm pitch, pogo-friendly |

Exact values need bench confirmation against a real phone's NFC field strength
and the chosen piezo load.

## Firmware

### Environment

Bare-metal C, or a lightweight Arduino core for AVR megaTinyCore / tinyAVR
0/1-series devices. Prefer the smallest runtime that still gives reliable
timer and sleep control.

### Power rules

- Clock the MCU slowly (around 1 MHz) unless measurements show you need more
  CPU for timer setup.
- Prefer hardware timers for square-wave generation. Don't bit-bang the piezo
  in a busy loop.
- Avoid long blocking delays that keep the core awake for no reason. Drive
  note timing from a timer interrupt or a sleep-friendly wait.
- After the melody ends, enter the deepest sleep the part supports and stay
  there until the phone leaves and the rail collapses.

### Note data

Store melodies as static arrays in Flash. Each note is:

```c
typedef struct {
  uint16_t frequency_hz; /* 0 = rest */
  uint16_t duration_ms;
} Note;
```

Rough capacity at 4 bytes per note: on the order of 1,500 notes in 8 KB Flash
before code and other constants eat the budget. Keep a few kilobytes free for
startup, timer setup, and sleep.

### Boot and play sequence

1. Power appears on `VOUT` when the phone's NFC field couples to the antenna.
2. MCU boots. Wait out the hardware RC delay (about 120 ms) so the MOSFET
   gate timing has expired and connecting bulk capacitance is safe.
3. Drive the MOSFET gate low to connect the 10 µF capacitor.
4. Walk the melody array. For each note, program the PWM / timer frequency and
   enable differential (or single-ended) piezo drive for `duration_ms`.
5. When the array ends, stop the PWM outputs and enter deep sleep.
6. Removing the phone drops RF power and resets the board for the next tap.

## Form factor and layout

Antenna area dominates the outline. Expect something from about 25 mm × 25 mm
(postage-stamp) up to credit-card size, depending on how much flux you need
from weak phone fields.

Layout constraints:

- Don't put continuous ground planes over the antenna's interior. They induce
  eddy currents that kill coupling.
- Minimize large closed copper loops inside the antenna keep-out.
- Keep the board low-profile: QFN MCU, 0402 passives, SMD piezo, no tall
  electrolytics.
- Route the gated bulk capacitor and MOSFET close to the MCU and piezo so the
  high-current PWM path is short.

## KiCad project

Schematic and board live under [`kicad/`](kicad/). Open
`kicad/tinynfc.kicad_pro` in KiCad 7 or later.

| Decision | Choice in this revision |
|----------|-------------------------|
| MCU | ATtiny816-MNR (VQFN-20) |
| Piezo drive | Differential on PB0 / PB1 |
| Hard-tied `VOUT` cap | 100 nF (under the 220 nF NXP limit) |
| Board size | 40 mm × 40 mm |
| Antenna | 28 mm rectangular spiral on `F.Cu` (~2.75 µH target) |

Connectivity in the schematic is by net labels. After opening the project,
run **Update PCB from Schematic**, then route. The generator places
footprints and draws the spiral; it does not auto-route.

Regenerate from the design inputs with:

```bash
python3 tinynfc/kicad/scripts/generate_project.py
```

## Open questions

These need decisions or measurements before locking the schematic:

- Exact series resistor after measuring piezo current spikes on NFC power.
- Antenna geometry for reliable coupling across common phone NFC coil
  placements (confirm inductance on a VNA).
- Whether the NTAG's I2C / EEPROM side is used for anything (melody select,
  config) or left unused with the chip acting only as a harvester and tag.
- Melody format extensions (volume, duty cycle, envelopes) versus staying at
  two `uint16_t` fields per note.
- Confirm XQFN8 / DFN1006 land patterns against manufacturer drawings before
  fab.

## Out of scope (for now)

- Polyphonic audio or DAC-based synthesis.
- Batteries, supercaps that stay charged after the phone leaves, or USB
  power in normal use.
- A plastic enclosure or sticker art (mechanical stack can follow once the
  PCB outline is stable).
- Shipping firmware update over NFC. Field programming is UPDI only in this
  revision.
