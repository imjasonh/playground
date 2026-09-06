# Design: inkbot-magsafe, a MagSafe e-ink tile

> **Status: 0.1.0, hardware design, not yet built.** A 4-inch mono e-ink tile
> that snaps to the MagSafe ring on the back of an iPhone. An iOS app pushes
> frames to it over Bluetooth Low Energy (BLE), on demand or in the background.
> It runs off a tiny lithium-polymer (LiPo) cell and tops off wirelessly when
> the phone-plus-tile stack sits on a charger. This doc is the circuit, the bill
> of materials (BOM), and the pricing. The companion BOM lives in
> [`inkbot-magsafe-bom.csv`](inkbot-magsafe-bom.csv).

This is a sibling to the existing [`inkbot-esp32/`](../inkbot-esp32/) firmware.
That device is a tethered 7.5-inch panel that joins Wi-Fi and polls the
[`inkbot/`](../inkbot/) Worker. This one drops Wi-Fi and the wall wart: it is
battery-first, phone-first, and talks BLE to a phone in your pocket.

## What the brief gets right, and the one thing it gets wrong

The battery math in the brief is sound. A 4-inch mono panel sips microamps
asleep and spends a few hundredths of a milliamp-hour per refresh, so a 100 mAh
cell is comfortable. The numbers below back that up.

The wrong assumption is the power source. **An iPhone does not send Qi power out
its back to an accessory stuck on the MagSafe ring.** Reverse wireless charging
to arbitrary accessories is not a feature Apple ships (the MagSafe Battery Pack
is a special case with its own handshake). So "infinite power whenever the phone
is picked up or set down" is not real. Power only arrives when the whole
phone-plus-tile stack is placed on a MagSafe or Qi charger, and even then only if
the tile either sits closest to the pad or relays power through to the phone.
That relay (pass-through charging) is the expensive, thick, hot part of this
product, and it fights all three stated goals: reliability, slimness, and
battery life.

So this design ships two variants, and I recommend the simpler one for the
stated priorities:

| | Variant S (self-charge) | Variant P (pass-through) |
|---|---|---|
| Tile charges from | its own Qi receive (RX) coil when the stack is on a pad | RX coil, taps the field it relays |
| Phone charges when stacked | no (tile blocks the pad) | yes, at 5 W through the tile |
| Added thickness | ~1 mm (thin RX coil) | ~2.5–3.5 mm (RX + transmit coil + shield + heat spread) |
| Peak heat under charge | low | meaningful; needs a thermistor and throttling |
| Regulatory lift | Qi RX (WPC + FCC Part 18) | Qi RX **and** TX; larger EMC and thermal test burden |
| Recommended for | reliability, slimness, battery life | the "never think about it" pass-through UX |

**Recommendation: build Variant S first.** The tile owns a tiny battery that
lasts weeks off charger (see the power budget), so "charge the tile" is a rare
event, not a daily chore. When the stack goes on a pad the tile tops itself off;
when you need the phone to charge, the tile's magnets let you pop it off in a
second. Variant P is a real option, but it turns a paper-thin accessory into a
warm coaster and adds a second coil, a transmit controller, and a thermal
budget. Ship it as a follow-on once the BLE and panel path are proven.

## Decisions (locked for 0.1.0)

| Topic | Decision |
|-------|----------|
| MCU / radio | **Nordic nRF52832** (or the Raytac MDBT42Q pre-certified module), not ESP32-C3 |
| Panel | 4.2-inch 400×300 mono e-ink, on-glass controller (SSD1683-class), partial refresh |
| Battery | 110–150 mAh LiPo pouch with protection, ~2 mm thick |
| Charger | **power-path** charger (TI BQ25100), not a bare MCP73831 |
| Panel power | fully gated by a load switch between refreshes |
| Wireless | Variant S: 5 W Qi RX only. Variant P: adds a 5 W Qi TX relay |
| Magnets | MagSafe-geometry N52 annular array; "MagSafe" naming needs Apple MFi |
| Link | BLE 4.2+ GATT for control, **L2CAP connection-oriented channel** for the frame blob |
| iOS delivery | Core Bluetooth central + State Preservation/Restoration, silent APNs wake, BGTasks |

### Why nRF52832, not the ESP32-C3 in the brief

The brief names an ESP32-C3. It works, and it is cheap, but it is the wrong tool
for a battery-first BLE peripheral that must stay reachable in the background:

- **Deep sleep is not the interesting number; connected idle is.** To catch a
  background push, the tile has to hold a BLE connection or advertise. On the
  nRF52832 a maintained connection with slave latency averages roughly 10–30 µA.
  The ESP32-C3 keeps its radio state in light sleep, not deep sleep, and connected
  light-sleep current is an order of magnitude higher.
- **The Nordic SoftDevice is a mature, qualified BLE stack** with good long-lived
  connection behavior; the e-ink hobbyist and product world runs on it.
- **It runs straight off the cell.** The nRF52 internal DC/DC converter accepts
  1.7–3.6 V, so a 3.0–4.2 V LiPo needs no regulator for the MCU.
- **Built-in NFC tag (NFCT)** gives an almost-free "tap to pair / open the app"
  path with a two-turn antenna.

The 52832 has 64 KB RAM and 512 KB flash: plenty for a 15 KB mono framebuffer
plus the S132 SoftDevice. Step up to the nRF52833 (128 KB RAM) only if you add
grayscale (a 4-level frame is ~30 KB) or want BLE Long Range (Coded PHY).

For the first prototypes, BOM the **Raytac MDBT42Q** module: it carries the
crystal, matching network, and antenna, and it is FCC/CE/MIC/BLE-SIG
pre-certified, which removes an intentional-radiator certification from the
critical path. Move to the bare QFN chip for cost only once volume justifies a
fresh RF layout and certification.

## Block diagram

```
                 ┌─────────────────────────────────────────────┐
   MagSafe ring  │  nRF52832 (MDBT42Q module)                  │
   magnets ──────┤   ├─ SPI ─────────► 4.2" e-ink COG (SSD1683)│
                 │   ├─ GPIO ────────► TPS22860 load switch ────┼─► panel 3.3V rail
   Qi RX coil ─► │   ├─ NFCT ────────► NFC "tap to pair" antenna│    (+ 220µF bulk)
   (BQ51013B) ─┐ │   └─ SAADC ───────◄ battery + thermistor     │
               │ └─────────────────────────────────────────────┘
   5V(RX out) ─┼──► BQ25100 power-path charger ──► LiPo 110mAh ──► VSYS ─► nRF (DC/DC)
               │        ▲                                   ▲
   USB-C ──────┘        │ ISET (charge ≈ 50–90mA)           │ protection FET
   (charge + SWD/DFU)   └─ NTC thermistor (charge safety)   └─ 220µF bulk near panel

   Variant P only:  Qi RX out ─► P9242-class TX controller ─► TX coil ─► phone
```

Signal notes: the panel is a bare chip-on-glass (COG) module on a 24-pin 0.5 mm
flex (FPC); its on-glass charge pump makes its own gate and source rails from
3.3 V, so the board only owes it a clean 3.3 V rail and a handful of reservoir
caps on the FPC pins. The load switch cuts that rail to zero between refreshes so
the panel contributes nothing to sleep current.

## Power budget

Assume a realistic day: the tile is off charger 8 hours, holds a background BLE
connection the whole time, and does 24 refreshes (a new frame roughly every
20 minutes plus a few on-demand pushes).

| Draw | Current / cost | Over the 8 h | Notes |
|---|---|---|---|
| nRF connected idle (1 s interval, slave latency) | ~20 µA avg | 0.16 mAh | radio kept alive to catch pushes |
| Panel + logic asleep (load switch open) | ~1 µA | ~0 mAh | panel fully gated |
| One full refresh | ~15 mA for ~2 s = 0.008 mAh | (per event) | mono 400×300, full update |
| One partial refresh | ~10 mA for ~0.7 s = 0.002 mAh | (per event) | most updates are partial |
| 24 refreshes (say 6 full, 18 partial) | | ~0.09 mAh | |
| BLE frame transfer (15 KB, L2CAP) | ~5 mA for ~3 s = 0.004 mAh | ~0.02 mAh | a few per day |
| **Daily off-charger total** | | **~0.27 mAh** | |

A 110 mAh cell holds roughly **400 days** of that daily reserve with no
recharge at all. The battery is not the constraint. Even a 60 mAh cell would do;
110–150 mAh is chosen for pouch availability and spike headroom, not runtime.

The real electrical risk is not capacity, it is the **refresh current spike from
a high-impedance tiny cell**. A 110 mAh pouch can have 1–2 Ω of internal
resistance; a 15 mA step is fine, but the panel's charge-pump inrush plus a radio
event can briefly pull more and sag VSYS enough to brown out the nRF. The fix is
cheap and non-negotiable: a **220 µF bulk capacitor** at the panel rail and a
power-path charger so charge/discharge transitions never drop the system rail.

## Circuit design

### Power path

Use a **power-path** charger, the TI BQ25100, not a bare MCP73831. The MCP73831
in the brief is a fine linear charger, but it has no system output: it sits
between the source and the battery, so the load hangs directly on the cell and
sees every transient. The BQ25100 powers the system from the input when input is
present and switches to battery seamlessly when it is removed. That "instant
cutover" the brief describes is exactly what a power-path IC gives you for free,
and it is the difference between a reliable tile and one that resets when you lift
the phone off a charger mid-refresh. Set charge current low (50–90 mA) with the
ISET resistor to be kind to the small cell; there is no reason to fast-charge a
battery that drains a fraction of a milliamp-hour a day.

Two charge inputs feed it, OR-ed with Schottky or an ideal-diode load switch:

- **USB-C** on the tile edge, for factory bring-up, SWD/DFU, and manual charging.
- **Qi RX output** from the BQ51013B 5 W receiver (both variants).

The nRF52832 runs directly from VSYS through its internal DC/DC (add the DC/DC
inductor and caps per Nordic's reference). The panel gets a dedicated 3.3 V rail
behind a **TPS22860 load switch** driven by a GPIO, so idle current is just the
nRF plus leakage.

### Wireless power

Variant S uses the **BQ51013B** (or NXP equivalent) with a MagSafe-profile RX
coil sized to Apple's ring geometry so it aligns on any MagSafe pad. Route the
coil on the back layer, keep a ferrite shield between the coil and the PCB ground
plane, and keep the 2.4 GHz antenna in the opposite corner from the coil and
magnets (both detune it).

Variant P adds a Qi **transmit** stage (a P9242-class TX controller and TX coil)
fed from the RX output, relaying ~5 W to the phone. This is where the thickness,
heat, and EMC work live. Add an NTC thermistor under the coil stack and throttle
or fold back TX power above ~45 °C. Do not attempt 15 W: Apple caps non-MFi
accessories to 7.5 W, and 5 W keeps the thermal story sane behind a phone.

### Antenna and the phone-metal problem

A phone's metal chassis and the MagSafe magnet array sit millimeters from the
radio and will detune a 2.4 GHz antenna. Two consequences drive the layout:

- Put the antenna (module or chip) at the tile edge farthest from the magnet
  ring, with a ground keep-out under it.
- **Tune with a phone attached**, not on the bench. Final matching-network
  values must be picked with the tile in its real dielectric environment.

### Board stack

A 4-layer PCB (signal / ground / power / signal), ~0.8 mm, is worth the small
cost premium: it keeps a solid reference plane under the radio and the SPI runs,
which matters more here than in a hobby build because the antenna is already
compromised by the phone. Board outline follows the panel (~91 × 77 mm). The
panel adheres to the front; battery, coil, and magnet ring stack on the back.

### Realistic thickness

Paper-thin is aspirational. Honest stack-ups:

| Layer | Variant S | Variant P |
|---|---|---|
| E-ink panel + FPC | 1.0 mm | 1.0 mm |
| PCB | 0.8 mm | 0.8 mm |
| LiPo cell | 2.0 mm | 2.0 mm |
| RX coil + ferrite | 0.6 mm | 0.6 mm |
| TX coil + shield | (none) | 1.2 mm |
| Magnet ring + skins/adhesive | 0.8 mm | 0.8 mm |
| **Total (approx.)** | **~4.5 mm** | **~5.8 mm** |

That is thicker than a MagSafe wallet but thinner than a battery pack. The
"under 2 mm" figure in the brief describes the bare cell, not the finished tile.

## BLE and iOS integration

The tile is a BLE peripheral (GATT server). The iOS app is the central. See the
[`ios/`](../ios/) app; this ships as a new experiment there rather than a new
top-level app.

### GATT layout

| Characteristic | Properties | Purpose |
|---|---|---|
| Control | write | begin frame, region, full-vs-partial, commit |
| Status | read / notify | battery %, charge state, temperature, last-refresh result |
| Frame (fallback) | write-without-response | chunked pixel data when L2CAP is unavailable |

For the pixel payload, prefer an **L2CAP connection-oriented channel**
(`CBL2CAPChannel` on iOS). A 400×300 mono frame is 15 KB; over an L2CAP stream
with a negotiated MTU that is a couple of seconds, versus a slow parade of
20-byte GATT writes. Keep the GATT "Frame" characteristic as a fallback for
centrals that will not open a channel.

### Getting a frame there in the background

iOS does not let an app run arbitrary code on a schedule to poke BLE. Truly
"push any time" is not something iOS guarantees. What it does give you, and the
tile should be designed around, is a combination:

- **Persistent connection + State Preservation and Restoration.** With the
  `bluetooth-central` background mode, iOS keeps a connection alive and relaunches
  the app to handle events (`willRestoreState`, notifications) even after the app
  is jettisoned. The tile stays connected and the app is woken briefly to write a
  new frame.
- **Silent push (APNs `content-available`).** The tile's data source (for example
  the inkbot Worker) sends a background push to the phone; the app wakes, connects
  to the retained peripheral by identifier, and pushes the frame.
- **`BGAppRefreshTask` / `BGProcessingTask`.** For non-urgent updates, the app
  wakes on the system's schedule and syncs.
- **Peripheral-initiated nudge.** If the tile wants attention (a button, or it
  woke on its own timer), it advertises a specific service UUID; iOS background
  scanning for that UUID relaunches the app. Background scans must name the UUID
  (no wildcard) and are duty-cycled, so treat this as "within a minute," not
  instant.

Design the protocol so a push is idempotent and resumable: the app sends a frame
id and a hash, the tile acknowledges what it already has, and a dropped
connection resumes rather than restarts. Background BLE windows are short; a
15 KB transfer must survive being interrupted and continued on the next wake.

On demand (app in foreground) is the easy case: connect, open the L2CAP channel,
stream, commit, done.

## Firmware

Reuse the shape of [`inkbot-esp32/`](../inkbot-esp32/) where it helps, but this is
a fresh crate for the nRF target (nRF52 SoftDevice via `nrf-softdevice`, or a
C/Zephyr build if the panel vendor's driver is easier to port). Core pieces:

- **Panel driver**: SPI to the SSD1683-class COG, full and partial LUTs, forced
  full refresh every N partials to clear ghosting.
- **BLE peripheral**: the GATT table above plus the L2CAP server; low duty-cycle
  advertising when disconnected.
- **Frame store**: keep the last frame in flash so the tile can repaint after a
  battery swap or a crash without waiting for the phone.
- **Power manager**: gate the panel rail, keep the radio in the lowest connected
  state that still meets the latency target, sample battery and temperature on
  the SAADC, report them over Status.
- **DFU**: BLE DFU (Nordic Secure DFU) so updates arrive over the same link as
  frames; USB-C is the recovery path.

Firmware does not need the OTA-from-GHCR or GCP machinery the Wi-Fi device
carries; the phone is the update transport.

## Bill of materials and cost

Full line items with part numbers and price columns are in
[`inkbot-magsafe-bom.csv`](inkbot-magsafe-bom.csv). Rolled-up cost of goods
(COGS) at ~1,000 units, using the pre-certified radio module:

| | Variant S | Variant P |
|---|---|---|
| Parts | ~$29 | ~$37 |
| Assembly (SMT, test) | ~$4 | ~$5 |
| **COGS** | **~$33** | **~$42** |
| Suggested retail (2.5–3×) | ~$85–99 | ~$119–129 |

The panel (~$12), the radio module (~$4.2), and the Qi receive stage (~$4.6 for
the receiver plus coil) dominate Variant S. Dropping to a bare nRF52832 QFN saves
~$2 in parts but costs an RF layout and a certification cycle; do that only at
volume. Variant P's ~$8 adder is almost entirely the transmit coil and controller
plus the thermal parts.

## Reliability checklist

- Power-path charger so lift-off-charger transitions never brown out the nRF.
- 220 µF bulk cap at the panel rail to absorb refresh inrush from a high-ESR cell.
- Antenna tuned with a phone attached; ground keep-out under it.
- NTC thermistor for charge safety (both variants) and TX throttling (Variant P).
- Cell with an integrated protection FET, or add a DW01 + dual FET.
- ESD protection (TVS array) on the USB-C data and power pins.
- Forced periodic full refresh to prevent e-ink ghosting.
- Note the operating range: e-ink refresh is unreliable below ~0 °C.

## Regulatory and MFi

- **"MagSafe" is Apple's mark.** Selling something that fits Apple's magnet
  geometry is fine; calling it MagSafe, drawing 15 W, or showing the on-screen
  charging ring needs Apple's MFi program (which adds an authentication IC and
  licensing). Without MFi: generic magnets, "works with MagSafe chargers,"
  7.5 W cap.
- The pre-certified radio module clears the intentional-radiator certification.
- The Qi coil is still a Part 18 radiator; Variant P's transmitter roughly
  doubles the EMC and thermal test burden and may want WPC (Qi) certification.

## Open questions

- Mono only, or a BWR / grayscale variant? Grayscale pushes to the nRF52833 and
  larger frames.
- Is pass-through charging a launch requirement, or a v2? The recommendation is
  v2; Variant S ships the better product against the stated goals.
- Does the frame source stay the inkbot Worker (silent push from the same place
  that feeds the Wi-Fi device), or is the phone the sole source of truth?
