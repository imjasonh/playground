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
| MCU / radio | **Raytac MDBT50Q-512K** — pre-certified nRF52833 module (128 KB RAM for the 48 KB framebuffer; integrated antenna, 32 MHz crystal, DC/DC, RF match) |
| Panel | **3.97-inch 480×800 portrait** mono e-ink, on-glass controller (SSD1677), partial refresh |
| Orientation | portrait; ring high on the tile, panel fills the tile and overlaps the ring |
| Battery | ~120 mAh thin LiPo pouch with protection, ~1.5 mm, in a PCB cutout below the coil |
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

### Why nRF52833, not the ESP32-C3 in the brief

The brief names an ESP32-C3. It works, and it is cheap, but it is the wrong tool
for a battery-first BLE peripheral that must stay reachable in the background:

- **Deep sleep is not the interesting number; connected idle is.** To catch a
  background push, the tile has to hold a BLE connection or advertise. On the
  nRF52 a maintained connection with slave latency averages roughly 10–30 µA.
  The ESP32-C3 keeps its radio state in light sleep, not deep sleep, and connected
  light-sleep current is an order of magnitude higher.
- **The Nordic SoftDevice is a mature, qualified BLE stack** with good long-lived
  connection behavior; the e-ink hobbyist and product world runs on it.
- **It runs straight off the cell.** The nRF52 internal DC/DC converter accepts
  1.7–3.6 V, so a 3.0–4.2 V LiPo needs no regulator for the MCU.

The design uses the **nRF52833** rather than the 52832 because the 3.97-inch
panel needs a **48 KB mono framebuffer** (480×800). The 52832's 64 KB RAM is too
tight once the SoftDevice takes its share; the 52833's **128 KB** holds the
frame plus the S132/S140 stack comfortably.

The nRF52833 ships as a **pre-certified module, the Raytac MDBT50Q-512K**, not a
bare QFN. The module integrates the 2.4 GHz antenna, the 32 MHz crystal, the
DC/DC inductors, and the RF matching network, and carries FCC/IC/CE/MIC/KC/SRRC
modular approval. That removes the whole radio-layout problem — no antenna
keep-out to tune, no matching network to pick with a phone attached, no
intentional-radiator certification to run — at the cost of ~1 mm of thickness
(the module is ~2 mm tall). The board owes it only a VDD/VDDH bypass and a
32.768 kHz crystal on P0.00/P0.01 for low-power BLE timing (the module leaves the
LFXO external). No NFC: pairing and frames are BLE-only, so the NFCT pins (P0.09/
P0.10) stay unused.

## Block diagram

```
                 ┌─────────────────────────────────────────────┐
   MagSafe ring  │  Raytac MDBT50Q-512K (nRF52833 module)      │
   magnets ──────┤   ├─ SPI ─────────► 3.97" e-ink COG (SSD1677)│
                 │   ├─ GPIO ────────► TPS22810 + MIC5504 ──────┼─► panel 3.3V rail
   Qi RX coil ─► │   ├─ SAADC ───────◄ battery + thermistor     │    (+ 220µF bulk)
   (in magnet    │   └─ (antenna + 32MHz + DC/DC on-module)      │
    ring)        └─────────────────────────────────────────────┘
        │
        └─► BQ51050B (Qi RX + charger) ──► LiPo ~120mAh (PCB cutout) = VSYS ─► module VDD
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

### Why 3.97-inch, portrait

The tile has to fit an iPhone's back **without hanging over the sides or the
bottom**, and without fouling the camera plateau. With the minis dropped, the
width target is a standard/Pro iPhone at ~70.6 mm. The height budget is tighter:
Apple's MagSafe keep-in puts the tile top ~43 mm from the phone top on a 15 Pro
(146.6 mm tall), leaving only **~104 mm** of vertical room.

| Panel | Module (portrait) | Width fit (70.6) | Height fit (~104) |
|-------|-------------------|------------------|-------------------|
| 4.2" GDEY042T81 | 77 × 91 | overhang | — |
| **4.26" GDEY0426T82** | 62 × 105 | fits | **overhangs bottom** |
| **3.97" GDEY0397T81P** | **56 × 97** | **fits** | **fits** |
| 3.7" GDEY037T03 | 53 × 93 | fits | fits (smaller) |

The **3.97-inch 480×800** module is the largest common mono e-paper that clears
both axes on a 6.1" Pro. Same resolution and SSD1677 controller as the 4.26";
only the glass is shorter. A 480×800 mono frame is still **48 KB**, which is why
the MCU is the nRF52833 (128 KB).

## Power budget

Assume a realistic day: the tile is off charger 8 hours, holds a background BLE
connection the whole time, and does 24 refreshes (a new frame roughly every
20 minutes plus a few on-demand pushes).

| Draw | Current / cost | Over the 8 h | Notes |
|---|---|---|---|
| nRF connected idle (1 s interval, slave latency) | ~20 µA avg | 0.16 mAh | radio kept alive to catch pushes |
| Panel + logic asleep (load switch open) | ~1 µA | ~0 mAh | panel fully gated |
| One full refresh | ~15 mA for ~2 s = 0.008 mAh | (per event) | mono 480×800, full update |
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

The module runs directly from VSYS on its `VDD`/`VDDH` pins; the DC/DC inductor
and its decoupling live inside the module, so the board only adds a VDD/VDDH
bypass. The panel gets a dedicated 3.3 V rail behind a **TPS22810 load switch**
and **MIC5504-3.3** LDO driven by a GPIO, so idle current is just the module plus
leakage.

### Wireless power

The **BQ51050B** drives a MagSafe-profile RX coil sized to Apple's ring geometry
so the tile self-aligns on any MagSafe pad. Place the coil inside the magnet
ring on the back, keep ferrite between the coil and the board, and orient the
module so its integrated antenna faces the tile edge farthest from the ring
(magnets and coil both detune 2.4 GHz). There is no transmit stage: the tile
charges itself, not the phone.

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
radio and detune a 2.4 GHz antenna. The pre-certified module fixes the *design*
half of this — the antenna and its match are done and certified on the module —
but not the *physics*: the magnets still pull the tuning. So the layout still:

- Places the **module with its antenna end at the tile edge farthest from the
  magnet ring**, over the board edge, with the copper keep-out the module
  footprint already defines under the antenna.
- Expects some **range loss** with the magnets so close. At BLE distances (a
  phone touching the tile) there is large link margin, so this is acceptable;
  the module's certification stays valid because its antenna and matching are
  unchanged. No board-side matching network to tune.

### Board stack

A 4-layer PCB (signal / ground / power / signal), **60 × 99 mm portrait**, with a
**battery cutout** below the coil so the cell does not stack on the FR4. The
volume target is **0.4 mm**; the first prototype is **0.8 mm** because that is
the 4-layer floor at the cheap fabs (JLCPCB, PCBWay standard) — 0.4 mm 4-layer
needs an advanced fab. The 0.8 mm proto only grows the ring region by ~0.4 mm
(the battery sits in a cutout, so its region is unchanged), so it is the right
board to validate function first. The 3.97-inch panel is bonded to the whole
front and **overlaps the MagSafe ring**: the coil and magnets are on the back,
the panel on the front, so they share the same footprint without colliding. No
case for 0.1.0. See
[`inkbot-magsafe/kicad/`](../inkbot-magsafe/kicad/) for the schematic and
outline, and
[`inkbot-magsafe/hardware/stackup.md`](../inkbot-magsafe/hardware/stackup.md)
for the mechanical stack.

Because the panel covers the front, the module, BQ51050B, and passives mount on
the **back**, ringing the coil and the cutout, inside the magnet-ring thickness
envelope.

### Realistic thickness

Thickness-first layout (cutout + thin PCB + module + combined Qi/charger). The
module (~2 mm tall) is now the tallest back-side part, so it, not the battery,
can set the thickest point:

| Region | Approx. |
|--------|---------|
| At the module (panel + 0.8 mm PCB + ~2 mm module) | **~3.05 mm** |
| At the cell (panel + 1.5 mm LiPo in cutout) | **~2.55 mm** |
| At the magnet ring (panel + 0.8 mm PCB + coil/magnets/parts) | **~2.4 mm** |

The pre-certified module trades ~1 mm of thickness for deleting the entire radio
layout and certification. The bare-QFN alternative lands near ~2.55 mm but owes
antenna tuning and an intentional-radiator cert. Pass-through TX would still add
~1.2 mm and is rejected. This is the accepted trade for 0.1.0.

### Fabrication and first build

Who builds what:

- **PCB + SMT assembly (PCBA)** — one vendor. **JLCPCB** (cheapest, rigid
  automation) or **PCBWay** (pricier, more hand-holding and sourcing) both fab
  the board and place the surface-mount parts, including the Raytac module, the
  leadless BQ51050B, and the passives. Deliver Gerbers, BOM, and a centroid/
  pick-and-place file (all exported from the KiCad project).
- **Panel, coil, magnets, battery** — not reel parts an assembler drops in for a
  one-off. Bonding the e-ink glass to the front, placing the Qi coil and MagSafe
  magnet ring on the back, and attaching the LiPo are bench work. PCBWay
  turnkey/box-build can source and attach some of these; JLCPCB generally will
  not.

The KiCad project is **routed** by `kicad/layout_route.py`: it places the parts,
pours the In2/B.Cu ground and In1 VSYS planes, and maze-routes the signal nets
(most auto-route; a couple are left as ratsnest for manual finishing), then
exports Gerbers, drill, and centroid. The module is pre-certified, so there is
no antenna match to tune. Open the project and **run DRC in the KiCad GUI**,
finish any remaining ratsnest, and verify impedance before a production order.

Recommended one-off sequence (validate function before optimizing thickness):

1. **Breadboard, no custom PCB.** An nRF52833/52840 devkit (or Feather nRF52) +
   the GDEY0397T81P on its Good Display DESPI FPC adapter + a LiPo. Proves the
   SSD1677 driver, the 480×800 framebuffer, BLE push, and power behavior with no
   bonding.
2. **One-off tile.** ~5 boards, **PCBA, 0.8 mm 4-layer, ENIG** from JLCPCB (or
   PCBWay if you want them to source the odd parts). Buy the panel, a MagSafe
   magnet ring + Qi RX coil, and a ~120 mAh protected LiPo separately, then
   hand-integrate. Bring up over the SWD test pads.

The design already uses the **pre-certified Raytac MDBT50Q-512K module**, so the
radio works out of the box on the first tile — no antenna tuning, no crystal, no
RF certification. A future thickness optimization could move to a bare nRF52833
QFN (~1 mm thinner) once everything else is proven, at the cost of taking on the
antenna layout and an intentional-radiator cert.

### Phone compatibility and fit

Two things gate compatibility: the phone must have the **MagSafe magnet ring**
(magnet-only retention), and the tile (**60 × 99 mm**) must sit inside the body
in both axes — no side overhang, no bottom overhang, and clear of the camera
bump. The minis are dropped (too narrow); the 4.26" panel was tried and dropped
(too tall for a 6.1" Pro once the ring sits high enough to clear the cameras).

| iPhone | Body W × H (mm) | MagSafe | Side inset | Bottom clearance | Fits? |
|--------|-----------------|:---:|---:|---:|:---:|
| 16 / 15 Pro Max, 15/14 Plus, 14/13/12 Pro Max | 77.6–78.1 × 160–163 | yes | ~9 mm | lots | **yes** |
| 16 Pro | 77.6 × 149.6 | yes | ~9 mm | ~8 mm | **yes** |
| 16 / 15 / 14 / 13 / 12 (standard) | 71.5–71.6 × 147–148 | yes | ~5.8 mm | ~4 mm | **yes** |
| **15 Pro / 16 Pro** | **70.6 × 146.6–149.6** | yes | **~5.3 mm** | **~4 mm** | **yes** |
| 17 / 17 Pro / 17 Pro Max | 71.7–77.6 × 150–163 | yes | ≥5 mm | ≥4 mm | **yes** |
| **13 mini / 12 mini** | 64.2 × 131.5 | yes | overhang | — | **no** |
| iPhone 16e | 71.5 × 147.7 | **no** | — | — | **no** |
| SE (all), 11 and earlier | — | **no** | — | — | **no** |

A third-party MagSafe-magnet case can add the ring to a 16e or older phone.

**Camera clearance comes from Apple's own rule.** The Accessory Design
Guidelines require a MagSafe accessory not to extend past **30 mm from the ring
center toward the top of the phone**. So the tile puts the MagSafe ring **as
high as it can** — ring center 30 mm from the top edge — and hangs downward,
below the cameras. On a 15 Pro that puts the tile top ~43 mm from the phone top
and the bottom ~4 mm above the phone's bottom edge. The 4.26" panel (105 mm
module) would have hung ~4 mm past that edge; the 3.97" does not.

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
(`CBL2CAPChannel` on iOS). A 480×800 mono frame is 48 KB; over an L2CAP stream
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

- **Panel driver**: SPI to the SSD1677-class COG, full and partial LUTs, forced
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
(COGS) at ~1,000 units, thickness-first with the pre-certified module:

| | Shipping tile |
|---|---|
| Parts (incl. thin PCB) | ~$30 |
| Assembly (SMT, test) | ~$4 |
| **COGS** | **~$34** |
| Suggested retail (2.5–3×) | ~$90–99 |

The 3.97-inch panel (~$10.50), the module (~$4.50), and the Qi stage (~$4.8 for
BQ51050B + coil) dominate. The module costs ~$1.60 more than a bare nRF52833
(~$2.90) but folds in the antenna, crystal, and — critically — the intentional-
radiator certification, so it is cheaper once certification and RF spins are
counted. Pass-through TX would still add ~$8 and is rejected.

## Reliability checklist

- System on the cell via BQ51050B; charge while detached (no mid-refresh cutover).
- 220 µF bulk cap at VSYS near the panel connector for refresh inrush.
- Module antenna at the tile edge farthest from the ring; keep-out per the
  module footprint. No board-side match to tune (module is pre-certified).
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
- The design uses a **pre-certified module (Raytac MDBT50Q-512K)**, so it carries
  the module's FCC/IC/CE/MIC/KC/SRRC modular IDs and needs only unintentional-
  radiator (Part 15B) testing for the finished product, not a full intentional-
  radiator campaign.
- The Qi coil is still a Part 18 radiator. The tile is receive-only, so there is
  no transmit EMC burden; adding pass-through later would roughly double it and
  may want WPC (Qi) certification.

## Decisions taken since 0.1.0 draft

- **The phone is the sole source of frames.** No Worker, no server push. This
  keeps the system to one radio and one trust boundary, at the cost of sub-minute
  remote updates (see BLE background).
- **Mono panel.** Black/white only. Grayscale or color is a later variant.
- **3.97-inch 480×800 panel on the nRF52833.** Largest mono e-paper that fits a
  6.1" Pro in **both** width and height with the ring high (camera-clear). The
  4.26" was tried and dropped — it overhangs the bottom of a 15 Pro by ~4 mm.
  Minis are dropped (too narrow). The 48 KB frame is why the MCU is the 128 KB
  nRF52833.
- **Pre-certified module, not bare QFN.** The nRF52833 ships as a Raytac
  MDBT50Q-512K module: it folds in the antenna, 32 MHz crystal, DC/DC, and RF
  match with modular certification, deleting the radio-layout work for ~1 mm of
  added thickness. Accepted.
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
- **Thickness-first KiCad schematic.** Raytac MDBT50Q-512K module, BQ51050B
  (Qi+charger), 0.8 mm prototype PCB (0.4 mm volume target) with battery cutout,
  no case. Project under [`inkbot-magsafe/kicad/`](../inkbot-magsafe/kicad/).

The firmware and hardware scaffold live in
[`../inkbot-magsafe/`](../inkbot-magsafe/); the iOS app is deferred until they
are dialed in.

## Open questions

- Enclosure material and how the panel is bonded to the front (adhesive frame vs
  bezel clip), given magnet-only retention.
- Per-face `BGTask` cadence tuning: which faces (weather, health) warrant a
  `BGProcessingTask` versus a lighter `BGAppRefreshTask`, within the relaxed
  target?
