# Design: inkbot-magsafe, a MagSafe e-ink tile

> **Status: 0.1.0, hardware design, not yet built.** A 4-inch mono e-ink tile
> that snaps to the MagSafe ring on the back of an iPhone. The paired iPhone is
> the only source of frames; an iOS app pushes them over Bluetooth Low Energy
> (BLE), on demand or in the background. It runs off a tiny lithium-polymer
> (LiPo) cell and recharges by popping off the phone and sitting on any
> MagSafe or Qi pad. This doc is the circuit, the bill of materials (BOM), and
> the pricing. The companion BOM lives in
> [`inkbot-magsafe-bom.csv`](inkbot-magsafe-bom.csv).

This is a sibling to the existing [`inkbot-esp32/`](../inkbot-esp32/) firmware.
That device is a tethered 7.5-inch panel that joins Wi-Fi and polls the
[`inkbot/`](../inkbot/) Worker. This one drops Wi-Fi, the wall wart, and the
Worker: it is battery-first, phone-first, and talks BLE to a phone in your
pocket. The phone composes every frame.

## What the brief gets right, and the one thing it gets wrong

The battery math in the brief is sound. A 4-inch mono panel sips microamps
asleep and spends a few hundredths of a milliamp-hour per refresh, so a 100 mAh
cell is comfortable. The numbers below back that up.

The wrong assumption is the power source. **An iPhone does not send Qi power out
its back to an accessory stuck on the MagSafe ring.** Reverse wireless charging
to arbitrary accessories is not a feature Apple ships (the MagSafe Battery Pack
is a special case with its own handshake). So "infinite power whenever the phone
is picked up or set down" is not real. The tile runs on its own cell whenever it
is on the phone, on or off a charger.

### How it charges: detach and drop it on a pad

The tile carries its own 5 W Qi receive (RX) coil, and its MagSafe magnets do
double duty: they hold it to the phone, and they self-align it on a charger. To
recharge, **pop the tile off the phone and set it on any MagSafe or Qi pad.**
Because the battery lasts weeks off charger (see the power budget), this is an
AirPods-style occasional top-off, not a daily chore.

This is a deliberate choice to skip pass-through charging. When the phone sits on
a normal back-charging puck, the puck wants the phone's back, which is exactly
where the tile lives. Charging the phone *through* the tile would need a second
(transmit) coil stacked over the phone's receiver, plus a transmit controller and
a real thermal budget. That relay is the expensive, thick, hot part, and it
fights all three stated goals: reliability, slimness, and battery life. Detaching
to charge sidesteps it entirely.

**Rejected alternative: pass-through.** A version with an added Qi transmit stage
(a P9242-class controller and a stacked TX coil) could relay ~5 W to the phone so
you never detach. It adds ~1.5 mm, a hot spot behind the phone, an NTC thermistor
with power foldback, and a second radiator to certify. Revisit it only if
"never take it off" turns out to matter more than thinness; the battery math says
it should not.

## Decisions (locked for 0.1.0)

| Topic | Decision |
|-------|----------|
| MCU / radio | **Nordic nRF52832 bare QFN-48** (Raytac MDBT42Q optional later for cert) |
| Panel | 4.2-inch 400×300 mono e-ink, on-glass controller (SSD1683-class), partial refresh |
| Battery | ~100 mAh thin LiPo pouch with protection, ~1.5 mm, in a PCB cutout |
| Power | **BQ51050B** Qi RX + LiPo charger (one IC); system on the cell (detach-to-charge) |
| Panel power | fully gated by a load switch + 3.3 V LDO between refreshes |
| Charging | 5 W Qi RX only; detach the tile and set it on a pad. No pass-through |
| Frame source | the paired iPhone only; no Worker, no second radio |
| Port | none; SWD test pads for factory flash and recovery. USB-C considered and dropped |
| Enclosure | **none for 0.1.0** — panel is the front face |
| Magnets | MagSafe-geometry N52 annular array; magnet-only retention; "MagSafe" naming needs Apple MFi |
| Link | BLE 4.2+ GATT for control, **L2CAP connection-oriented channel** for the frame blob |
| iOS delivery | deferred until hardware is dialed in; Core Bluetooth central when built |
| Schematic | KiCad project under [`inkbot-magsafe/kicad/`](../inkbot-magsafe/kicad/) |

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

For thickness, the schematic BOMs the **bare nRF52832-QFAA** QFN-48 with discrete
32 MHz crystal, chip antenna, and matching. The Raytac MDBT42Q remains a drop-in
path later if intentional-radiator certification becomes the bottleneck.

## Block diagram

```
                 ┌─────────────────────────────────────────────┐
   MagSafe ring  │  nRF52832-QFAA (bare QFN)                   │
   magnets ──────┤   ├─ SPI ─────────► 4.2" e-ink COG (SSD1683)│
                 │   ├─ GPIO ────────► TPS22810 + MIC5504 ──────┼─► panel 3.3V rail
   Qi RX coil ─► │   ├─ NFCT ────────► NFC "tap to pair" antenna│    (+ 220µF bulk)
   (in magnet    │   └─ SAADC ───────◄ battery + thermistor     │
    ring)        └─────────────────────────────────────────────┘
        │
        └─► BQ51050B (Qi RX + charger) ──► LiPo ~100mAh (PCB cutout) = VSYS ─► nRF DC/DC
                 ▲                                              ▲
                 │ ILIM / FOD / TERM                            │ protection FET
                 └─ NTC (TS/CTRL + SAADC)                       └─ 220µF bulk near panel

   Recovery/factory only:  SWD pads (SWDIO/SWCLK/GND/VDD/NRST) ─► BLE-DFU + programming
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

Use the **BQ51050B**: one VQFN that is both the Qi receiver and the LiPo
charger. That removes a second power IC and its height from the stack. The
system hangs on the cell (`BAT` = `VSYS`). Charge while detached on a pad; do not
expect seamless source/battery cutover mid-refresh (refresh only runs when the
tile is awake on the phone, not while sitting on a charger). Cap charge current
with the ILIM resistor for the small cell.

There is no USB-C port on the shipping tile (see the next section).

The nRF52832 runs directly from VSYS through its internal DC/DC (DCC inductor
and DEC caps per Nordic's reference). The panel gets a dedicated 3.3 V rail
behind a **TPS22810 load switch** and **MIC5504-3.3** LDO driven by a GPIO, so
idle current is just the nRF plus leakage.

### Wireless power

The **BQ51050B** drives a MagSafe-profile RX coil sized to Apple's ring geometry
so the tile self-aligns on any MagSafe pad. Place the coil inside the magnet
ring on the back, keep ferrite between the coil and the board, and put the
2.4 GHz chip antenna at the opposite edge (magnets and coil both detune it).
There is no transmit stage: the tile charges itself, not the phone.

### Ports: none, by design

Ship the tile with **no connector at all.** Charging is wireless, and firmware
updates ride the same BLE link as frames (Nordic Secure DFU). A port is the part
most likely to fail on a thin accessory carried against a phone: it costs
thickness, invites water and lint, and adds a certification and a BOM line for a
job the wireless path already does.

The reliability backstop is a set of **SWD test pads** (SWDIO, SWCLK, GND, VDD)
on the back, under a peel label or the magnet ring, for factory programming on a
pogo fixture and for brick recovery when a BLE DFU goes wrong. DFU can fail, but
SWD always brings a board back.

USB-C was considered as a cabled charge and DFU fallback and dropped: with
wireless charge plus BLE DFU plus SWD recovery, the port earns nothing it does
not already have, and a sealed edge is thinner and more reliable.

### Antenna and the phone-metal problem

A phone's metal chassis and the MagSafe magnet array sit millimeters from the
radio and will detune a 2.4 GHz antenna. Two consequences drive the layout:

- Put the antenna (module or chip) at the tile edge farthest from the magnet
  ring, with a ground keep-out under it.
- **Tune with a phone attached**, not on the bench. Final matching-network
  values must be picked with the tile in its real dielectric environment.

### Board stack

A **0.4 mm** 4-layer PCB (signal / ground / power / signal) with a **central
battery cutout** so the cell does not stack on the FR4. Outline follows the
panel (~91 × 77 mm). No case for 0.1.0: the panel is the front face; coil and
magnets sit on the back. See [`inkbot-magsafe/kicad/`](../inkbot-magsafe/kicad/)
for the schematic and outline, and
[`inkbot-magsafe/hardware/stackup.md`](../inkbot-magsafe/hardware/stackup.md)
for the mechanical stack.

### Realistic thickness

Thickness-first layout (cutout + thin PCB + bare QFN + combined Qi/charger):

| Region | Approx. |
|--------|---------|
| At the cell (panel + 1.5 mm LiPo in cutout) | **~2.55 mm** |
| At the magnet ring (panel + 0.4 mm PCB + coil/magnets) | **~2.0–2.1 mm** |

Earlier ~4.5 mm assumed a 0.8 mm PCB and a cell under the board. Pass-through
TX would still add ~1.2 mm and is rejected. The "under 2 mm" figure in the brief
describes the bare cell, not the finished tile — this design lands near that
floor without a case.

### Phone compatibility and fit

Retention is magnet-only, so the tile fits any iPhone that carries the MagSafe
magnet ring: **iPhone 12 through iPhone 16**, every variant (mini, standard,
Plus, Pro, Pro Max). It does **not** fit phones without the ring — iPhone 11 and
earlier, every iPhone SE, and the **iPhone 16e** (Qi 7.5 W only, no magnets). A
third-party MagSafe-magnet case adds the ring to any of those.

The magnet array self-centers the tile on the ring; the phone model only changes
how far the 77 × 91 mm outline overhangs the body. Orient the 91 mm side along
the phone's length:

| Phone | Body W × H (mm) | Side overhang | Notes |
|-------|-----------------|---------------|-------|
| 16 Pro Max / 15 Plus / 14 Pro Max | ~77–78 × 160–163 | flush (±0.5) | best fit; tile inside the body |
| 15 / 16 / 14 / 13 / 12 (standard + Pro) | ~71.5 × 147 | +2.7 /side | small, even overhang |
| 13 mini / 12 mini | 64.2 × 131.5 | +6.4 /side | noticeable overhang |

Two real consequences, independent of model:

- **The tile overhangs the sides** on everything but the Plus/Max, because the
  panel is 84.8 mm across and the narrowest iPhones are ~64–71 mm. A smaller
  panel is the only way to sit fully within a standard body.
- **It rides up over the camera plateau.** The MagSafe ring sits above the
  phone's center, so a tile centered on it extends into the rear-camera area. On
  a real build, add a back-side pocket or accept that the tile covers the
  cameras while attached (it is a back accessory, not a case).

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
"push any time" is not something iOS guarantees, and with the phone as the sole
source there is no server to send a wake. So background updates are event-driven
and best-effort, and the launch faces are chosen to tolerate that: clock, the
day's calendar, weather, a health readout (steps or rings), a photo or custom
image, and custom text or a countdown. A best-effort notification or message
summary rides along, with the caveat that it lands on the next background wake,
not the instant a message arrives. Transit is deferred to a later face. What iOS
gives a source-on-device app:

- **Persistent connection + State Preservation and Restoration.** With the
  `bluetooth-central` background mode, iOS keeps a connection alive and relaunches
  the app to handle events (`willRestoreState`, notifications) even after the app
  is jettisoned. The tile stays connected and the app is woken briefly to write a
  new frame.
- **`BGAppRefreshTask` / `BGProcessingTask`.** The app wakes on the system's
  schedule (typically tens of minutes, adaptive to usage) to recompute a frame
  from on-device data and push it. This is the workhorse for a phone-only source.
- **Peripheral-initiated nudge.** If the tile wants attention (a button, or it
  woke on its own timer), it advertises a specific service UUID; iOS background
  scanning for that UUID relaunches the app, which then pushes. Background scans
  must name the UUID (no wildcard) and are duty-cycled, so treat this as "within
  a minute," not instant.

If a face ever needs sub-minute remote updates (an inbound message the instant it
lands), that requires a silent APNs push from some server, which the phone-only
model deliberately gives up. The notification-summary face is the likely reason
to add one later, so **reserve that path**: keep the tile firmware agnostic to
what wakes the app (it just receives a frame), and keep the app's push handling
behind one seam, so a future optional companion push service drops in without a
firmware change or a second radio. It is not built for launch.

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
  frames. SWD test pads are the brick-recovery path when a DFU fails; there is no
  USB port to fall back to.

Firmware does not need the OTA-from-GHCR or GCP machinery the Wi-Fi device
carries; the phone is the update transport.

## Bill of materials and cost

Full line items with part numbers and price columns are in
[`inkbot-magsafe-bom.csv`](inkbot-magsafe-bom.csv). Rolled-up cost of goods
(COGS) at ~1,000 units, thickness-first bare SoC:

| | Shipping tile |
|---|---|
| Parts (incl. thin PCB) | ~$28 |
| Assembly (SMT, test) | ~$4 |
| **COGS** | **~$32** |
| Suggested retail (2.5–3×) | ~$85–99 |

The panel (~$12) and the Qi stage (~$4.8 for BQ51050B + coil) dominate. The bare
nRF52832 (~$2.30) is cheaper than a pre-certified module; certification is a
later cost if you stay bare. Pass-through TX would still add ~$8 and is rejected.

## Reliability checklist

- System on the cell via BQ51050B; charge while detached (no mid-refresh cutover).
- 220 µF bulk cap at VSYS near the panel connector for refresh inrush.
- Antenna tuned with a phone attached; ground keep-out under it.
- NTC thermistor for Qi charge safety (shared with SAADC).
- Cell with an integrated protection FET, or add a DW01 + dual FET.
- SWD test pads for brick recovery, since there is no USB port to fall back to.
- Forced periodic full refresh to prevent e-ink ghosting.
- Note the operating range: e-ink refresh is unreliable below ~0 °C.

## Regulatory and MFi

- **"MagSafe" is Apple's mark.** Selling something that fits Apple's magnet
  geometry is fine; calling it MagSafe, drawing 15 W, or showing the on-screen
  charging ring needs Apple's MFi program (which adds an authentication IC and
  licensing). Without MFi: generic magnets, "works with MagSafe chargers,"
  7.5 W cap.
- The bare SoC needs intentional-radiator certification; swap to MDBT42Q if that
  becomes the bottleneck.
- The Qi coil is still a Part 18 radiator. The tile is receive-only, so there is
  no transmit EMC burden; adding pass-through later would roughly double it and
  may want WPC (Qi) certification.

## Decisions taken since 0.1.0 draft

- **The phone is the sole source of frames.** No Worker, no server push. This
  keeps the system to one radio and one trust boundary, at the cost of sub-minute
  remote updates (see BLE background).
- **Mono panel.** Black/white only, staying on the nRF52832. Grayscale or color
  is a later variant that would move to the nRF52833 for the larger frame.
- **Launch faces:** clock, calendar, weather, health, photo/image, custom text,
  and a best-effort notification summary. Transit is deferred.
- **Relaxed background cadence.** Target the iOS `BGTask` rhythm (roughly every
  15 to 30 minutes, adaptive), which is the best-battery choice; foreground
  updates are immediate. No tight always-on connection interval.
- **Push gap accepted, path reserved.** Phone-only for launch. The
  notification-summary face is the one that would justify an optional companion
  push service later, so the firmware and app are structured to add it without a
  redesign.
- **Charging is detach-and-drop on a Qi/MagSafe pad.** No pass-through in the
  shipping design.
- **No connector.** Wireless charge, BLE DFU for updates, SWD pads for recovery.
  USB-C was considered and dropped.
- **Magnet-only retention.** The MagSafe magnet ring holds the tile to the phone;
  no adhesive skin. The magnets already have to hold the tile on a charger, so
  they carry the phone too, and a magnet-only mount stays swappable between
  phones and cases.
- **A later push service stays independent.** If the reserved notification path
  is built, it is a private companion service, not the [`inkbot/`](../inkbot/)
  Worker and it shares no code with it. The tile firmware and app stay agnostic
  to the sender.
- **Thickness-first KiCad schematic.** Bare nRF QFN, BQ51050B (Qi+charger),
  0.4 mm PCB with battery cutout, no case. Project under
  [`inkbot-magsafe/kicad/`](../inkbot-magsafe/kicad/).

The firmware and hardware scaffold live in
[`../inkbot-magsafe/`](../inkbot-magsafe/); the iOS app is deferred until they
are dialed in.

## Open questions

- Enclosure material and how the panel is bonded to the front (adhesive frame vs
  bezel clip), given magnet-only retention.
- Per-face `BGTask` cadence tuning: which faces (weather, health) warrant a
  `BGProcessingTask` versus a lighter `BGAppRefreshTask`, within the relaxed
  target?
