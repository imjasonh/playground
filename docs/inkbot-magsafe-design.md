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
| Panel | **GDEM0397T81P**, 3.97-inch 480 x 800 portrait monochrome e-paper, SSD1677, partial refresh |
| Orientation | portrait; ring high on the tile, panel fills the tile and overlaps the ring |
| Battery | **LP252030 custom pack**, 100 mAh, protected, 10 kOhm NTC, keyed three-wire harness, up to 3.2 mm thick |
| Power | **BQ51013C** Qi 1.3 receiver into a **BQ25185** 40 mA charger with a SYS power path |
| Panel power | **TPS7A2030P** 3.0 V LDO, disabled with active discharge between refreshes |
| Charging | 5 W Qi RX only; detach the tile and set it on a pad. No pass-through |
| Frame source | the paired iPhone only; no Worker, no second radio |
| Port | none; SWD test pads for factory flash and recovery. USB-C considered and dropped |
| Enclosure | panel front face, structural spacer, electrical insulation, and a flame-retardant rear cover |
| Magnets | Apple accessory-array geometry, N48H ring, low-carbon-steel DC shield, and optional orientation magnet; magnet-only retention |
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
- **High-voltage mode accepts the SYS rail.** The BQ25185 powers `VDDH`; the
  nRF52833 REG0 stage creates its internal `VDD` rail. Factory provisioning sets
  UICR `REGOUT0` to 3.0 V before the application configures GPIO.

The design uses the **nRF52833** rather than the 52832 because the 3.97-inch
panel needs a **48 KB mono framebuffer** (480×800). The 52832's 64 KB RAM is too
tight once the SoftDevice takes its share; the 52833's **128 KB** holds the
frame plus S140 and the application.

The nRF52833 ships as a **pre-certified module, the Raytac MDBT50Q-512K**, not a
bare QFN. The module integrates the 2.4 GHz antenna, the 32 MHz crystal, the
DC/DC inductors, and the RF matching network, and carries FCC/IC/CE/MIC/KC/SRRC
modular approval. The module removes the board-side antenna matching network,
but it does not remove RF integration work. The PCB keeps copper out beneath
the antenna, places the antenna end at the board edge, and still needs host
product emissions and radiated-performance tests with the phone, magnets, and
coil installed. The module adds about 1 mm over a bare QFN and is about 2 mm
tall. The board adds separate VDDH and VDD capacitors plus a 32.768 kHz crystal
on P0.00/P0.01. The NFCT pins stay unused.

## Block diagram

```
   WR222230 coil -> BQ51013C -> QI_OUT -> BQ25185 -> SYS -> module VDDH
         |              |                    ^          |
      coil NTC       resonance/FOD           |          +-> 47 uF SYS reservoir
                                             |
   protected LP252030 pack + cell NTC -> BAT-+

   SYS -> TPS7A2030P 3.0 V -> 100 uF -> SSD1677 panel power and boost circuit
   MDBT50Q-512K <-> panel SPI, BUSY, reset, and panel-power enable
   MDBT50Q-512K <- Qi present and two charger-status signals

   Factory and recovery: SWDIO, SWDCLK, reset, VDD reference, SYS, and ground
```

Signal notes: the panel is a bare chip-on-glass (COG) module on a 24-pin 0.5 mm
flex (FPC); its on-glass charge pump makes its own gate and source rails from
3.0 V. The board implements the panel data sheet's external MOSFET, inductor,
diodes, sense resistor, and reservoir capacitors. The TPS7A2030P disables and
actively discharges the panel rail between refreshes.

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
| **3.97" GDEM0397T81P** | **56 × 97** | **fits** | **fits** |
| 3.7" GDEY037T03 | 53 × 93 | fits | fits (smaller) |

The **3.97-inch 480×800** module is the largest common mono e-paper that clears
both axes on a 6.1" Pro. Same resolution and SSD1677 controller as the 4.26";
only the glass is shorter. A 480×800 mono frame is still **48 KB**, which is why
the MCU is the nRF52833 (128 KB).

## Power budget

Assume the tile is off its charger for 24 hours, holds a background BLE
connection, and does 24 refreshes.

| Draw | Current / cost | Per day | Notes |
|---|---|---|---|
| nRF connected idle (1 s interval with slave latency) | ~20 uA average | ~0.48 mAh | Verify on the final connection parameters |
| BQ25185 in battery-only mode | ~4 uA typical | ~0.10 mAh | Charger data-sheet value |
| Panel LDO disabled | <1 uA budget | <0.03 mAh | Includes leakage margin |
| Six full and 18 partial refreshes | 36 mW typical while active | ~0.08 mAh | Full refresh is about 3 seconds; partial is about 0.3 seconds |
| Twenty-four 48 KB BLE transfers | ~5 mA for ~2 seconds each | ~0.07 mAh | Measure with negotiated 2M PHY, DLE, and L2CAP settings |
| **Daily electronics budget** | | **~0.8 mAh** | Excludes cell self-discharge and cold-temperature derating |

A new 100 mAh cell therefore has an ideal electronics-only runtime near
125 days. Capacity tolerance, aging, self-discharge, temperature, radio
retries, and reserve voltage reduce that number. The product target is
60-90 days between charges until measurements support a tighter claim.

The panel data sheet specifies a **120 mA typical peak current**, even though
its average refresh power is only about 36 mW. C38 adds 47 uF on SYS without
exceeding the BQ25185's 100 uF maximum, and C27 adds 100 uF at the panel within
the TPS7A20's 200 uF stability limit. Those parts do not prove margin. EVT must
capture BAT, SYS, PANEL_3V0, and current at room temperature, cold temperature,
end-of-charge, and the refresh floor. If the qualified LP252030 pack or its PCM
exceeds its pulse rating, use a higher-rate pack or revise pulse storage before
release.

## Circuit design

### Power path

The **BQ51013C** Qi receiver supplies 5 V to a **BQ25185** charger and
power-path manager. The BQ25185 separates `BAT` from `SYS`, blocks reverse
drain into the receiver, and supplements a weak input from the cell. R6 selects
a 4.2 V battery regulation voltage and a 100 mA input limit. R7 sets 40 mA fast
charge, within the LP252030 pack's 50 mA maximum.

There is no USB-C port on the shipping tile (see the next section).

`SYS` powers the Raytac module through `VDDH`. The nRF52833 REG0 stage creates
the internal 3.0 V `VDD` rail. The board does not use `VDD` as an external
power source. A **TPS7A2030P** creates the panel's 3.0 V supply and actively
discharges that rail while disabled.

### Wireless power

The **BQ51013C** uses a TDK WR222230-26M8-G 22 mm, 27 uH receiver coil inside
the magnetic ring. TI lists this coil for 50-500 mA receiver designs, while TDK
rates it for 2 W and does not claim that the coil alone is WPC compliant.
Starting resonance values are 81 nF series and 950 pF parallel. Measure `Ls`
and `Ls'` in the final stack, retune the capacitors, calibrate FOD, and test
interoperability across certified Qi transmitters.

The coil's ferrite faces the PCB. A separate 10 kOhm NTC bonded to the coil
connects to `TS/CTRL`. The receiver's current limit is about 250 mA nominal and
300 mA at the hardware limit. There is no transmit stage; the tile charges
itself, not the phone.

### Ports: none, by design

Ship the tile with **no user connector.** Charging is wireless, and the planned
signed DFU transport uses BLE. This choice is valid only after the bootloader,
owner-recovery flow, and update rollback tests pass.

The reliability backstop is a set of **SWD test pads** (SWDIO, SWCLK, GND, VDD)
on the back for factory programming and full-erase recovery. The rear cover must
define service access for the pogo fixture. Production readback protection must
preserve CTRL-AP erase recovery.

USB-C was considered as a cabled charge and DFU fallback and dropped. Revisit
that decision if BLE owner recovery or wireless charging fails reliability
testing.

### Antenna and the phone-metal problem

A phone's metal chassis and the magnetic array sit millimeters from the radio
and change the antenna pattern. The module supplies a qualified antenna and
matching network, but the host layout still controls its performance:

- The module's antenna end is flush with the left board edge, below and away
  from the magnetic ring.
- A 4.8 x 12 mm rule area blocks copper, tracks, and vias on every layer under
  the antenna.
- EVT must measure radiated performance with the complete magnetic, coil,
  battery, panel, and rear-cover stack. Test the tile both attached to and
  detached from every supported phone class.
- Submit the PCB layout to Raytac's layout-review service before release.

### Board stack

A 0.8 mm, four-layer PCB uses the JLC7628 stack with 1 oz outer and 0.5 oz
inner copper. In1.Cu is the SYS plane, and In2.Cu is ground. The routed
34 x 23 mm battery cutout has 1 mm corner radii. Standard vias are
0.6/0.3 mm, and copper stays 0.5 mm from every routed edge.

The 3.97-inch panel bonds to the front and overlaps the magnetic ring. The
back requires a rigid spacer and an insulating, flame-retardant cover. A future
0.4 mm board can reduce thickness after EVT, but it needs a different approved
fabricator stack and a complete DFM review. See
[`inkbot-magsafe/kicad/`](../inkbot-magsafe/kicad/) for the schematic and
outline, and
[`inkbot-magsafe/hardware/stackup.md`](../inkbot-magsafe/hardware/stackup.md)
for the mechanical stack.

The module, receiver, charger, LDO, and passives mount on the back below the
coil and around the cutout.

### Realistic thickness

The estimates include 0.10 mm front adhesive and a 0.25 mm rear cover:

| Region | Approx. |
|--------|---------|
| Module | **~4.07 mm** |
| Protected battery pack in the cutout | **~4.47 mm** |
| Magnet ring plus DC shield | **~3.27 mm** |
| Coil and ferrite | **~2.94 mm** |

The battery pack sets the baseline thickness. Adhesive tolerance, connector
clearance, cell swelling, and cosmetic films still need a mechanical tolerance
stack. An optional orientation magnet can add thickness if it overlaps the
cell, so the baseline uses the ring and a high-friction rear surface.

### Fabrication and first build

Who builds what:

- **PCB and SMT assembly.** JLCPCB or PCBWay can fabricate the 0.8 mm board and
  place the module, receiver, charger, panel power circuit, and passives. The
  release package needs Gerbers, drill data, fabrication and assembly drawings,
  an approved-vendor BOM, and a centroid file.
- **Final integration.** The panel, coil, magnet and shield assembly, protected
  battery pack, spacer, adhesive, and rear cover need a documented box-build
  process. The process must control FPC bend radius, cell compression, coil and
  thermistor adhesive, magnet polarity, insulation, and cure time.

`kicad/route_freerouting.py` places the parts, assigns nets, and adds solid
In1.Cu SYS and In2.Cu ground planes. It exports a Specctra DSN file, runs
Freerouting on F.Cu and B.Cu, imports the SES file, refills the planes, and
exports fabrication files. Every ground pad gets a via to In2.Cu; the outer
layers stay signal-only so disconnected pour islands cannot mask an open net.
`kicad/layout_route.py` contains the shared placement and fabrication rules.

Validate with `kicad/run_drc.py`, which calls KiCad's DRC engine through
pcbnew. `kicad/run_erc.py` checks the exact IC and connector pin contracts,
intentional no-connects, BOM coverage, and board-pad parity. Both checks must
pass on the release commit. They do not replace schematic review, DFM review,
or the bench validation table later in this document.

Recommended one-off sequence (validate function before optimizing thickness):

1. **Bench assembly.** Use an nRF52833 or nRF52840 development kit, the
   GDEM0397T81P vendor adapter, and a current-limited bench supply. Prove the
   panel sequence, measured current profile, BLE transport, and failure
   recovery before connecting a cell.
2. **EVT lot.** Build at least five 0.8 mm, four-layer ENIG assemblies. Use the
   exact panel, coil, custom protected pack, and magnetic assembly in the BOM.
   Program UICR and firmware over the SWD fixture, then run the electrical and
   mechanical acceptance tests on every unit.

The Raytac module avoids a board-side RF matching network. It does not make the
finished product automatically compliant or guarantee range beside a phone.
Keep the module for production unless a later bare-QFN program budgets a new RF
layout, antenna tuning, and intentional-radiator certification.

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
| Control | encrypted write with response | begin frame, region, full-vs-partial, commit, and resume offset |
| Status | read / notify | SYS estimate, charge state, panel temperature, and last-refresh result |
| Frame fallback | encrypted write without response | chunked pixel data when L2CAP is unavailable |

For the pixel payload, prefer an **L2CAP connection-oriented channel**
(`CBL2CAPChannel` on iOS) with a fixed PSM in the BLE LE dynamic range. A
480 x 800 monochrome frame is 48 KB. Negotiate 2M PHY, data-length extension,
and ATT MTU where available, then measure transfer time and energy. Keep the
GATT frame characteristic as a compatibility and wake-up fallback.

### Pairing and authorization

All control, frame, status, and DFU operations require an encrypted,
authenticated bond. On first boot, the panel displays a random passkey that
the app enters using LE Secure Connections. After pairing, the peripheral
accepts control only from the bonded identity and uses private addresses.

The frame CRC detects transfer corruption; it is not an authenticator.
Persist the last committed frame id with the frame metadata so a reboot does
not reopen the replay window. The product also needs a documented owner-reset
gesture that does not depend on the old phone. Until that gesture exists, SWD
erase is the only bond-recovery path and the firmware is not ready for users.

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

- **State preservation and restoration.** With the `bluetooth-central`
  background mode, iOS can restore the central and wake the app for documented
  Core Bluetooth delegate events. The app cannot assume continuous execution or
  an unlimited transfer window.
- **`BGAppRefreshTask` / `BGProcessingTask`.** The app wakes on the system's
  schedule (typically tens of minutes, adaptive to usage) to recompute a frame
  from on-device data and push it. This is the workhorse for a phone-only source.
- **Peripheral-initiated nudge.** If the tile wants attention (a button, or it
  woke on its own timer), it advertises a specific service UUID; iOS background
  scanning for that UUID relaunches the app, which then pushes. Background scans
  must name the UUID and are duty-cycled. The system does not guarantee a
  deadline, and it does not relaunch an app that the owner force-quit.

L2CAP stream callbacks alone have not been reliable wake sources on every iOS
release. Use a GATT notification to wake the central before resuming L2CAP, and
test the minimum supported iOS version in foreground, background, after
termination, after reboot, and after Bluetooth state restoration.

If a face ever needs sub-minute remote updates (an inbound message the instant it
lands), that requires a silent APNs push from some server, which the phone-only
model deliberately gives up. The notification-summary face is the likely reason
to add one later, so **reserve that path**: keep the tile firmware agnostic to
what wakes the app (it just receives a frame), and keep the app's push handling
behind one seam, so a future optional companion push service drops in without a
firmware change or a second radio. It is not built for launch.

The protocol rejects invalid or unaligned windows, mismatched lengths,
conflicting frame ids, stale ids, out-of-order chunks, and bad CRCs. A repeated
identical header returns the committed offset so a dropped transfer can resume.
Background BLE windows are short; a 48 KB transfer must survive interruption.

On demand (app in foreground) is the easy case: connect, open the L2CAP channel,
stream, commit, done.

## Firmware

The Rust crate reserves flash and RAM for S140 7.3.0. Host-tested code now
implements frame validation, replay checks, panel window rules, periodic full
refresh policy, charger-status decoding, voltage and temperature gates, and
the fail-closed UICR REGOUT0 policy.

The following target integrations remain release blockers:

- Configure panel power off and charge enabled before all other GPIO.
- Start S140 from the external 32.768 kHz crystal and implement bonded GATT plus
  the L2CAP server.
- Stream incoming data to an atomic flash record and seed the replay boundary
  from its committed metadata after reset.
- Implement the SSD1677 reset, two-RAM initialization, temperature-selected
  waveform, BUSY timeout, full and partial refresh, deep sleep, and rail
  discharge sequence.
- Sample `VDDHDIV5`, retain reset and brownout causes, and run a watchdog that
  also covers stalled panel and radio operations.
- Add a signed, power-fail-safe bootloader with a trial boot, rollback, and
  monotonic version floor. Size its active, update, state, and S140 partitions
  from the final linked image.
- Lock production debug against readout while preserving documented full-erase
  recovery through CTRL-AP and the SWD fixture.

BLE transports firmware from the phone. A CRC-only frame path and an unsigned
image are not acceptable DFU mechanisms.

## Bill of materials and cost

Full line items with part numbers and price columns are in
[`inkbot-magsafe-bom.csv`](inkbot-magsafe-bom.csv). The modeled direct build
cost includes parts, PCB fabrication, SMT, final integration, programming,
end-of-line test, spacer, insulation, and rear cover:

| Quantity | Unit direct cost | Build total | With 15% yield and price reserve |
|---:|---:|---:|---:|
| 1 | **$166.97** | **$167** | **$192** |
| 100 | **$59.61** | **$5,961** | **$6,855** |
| 1,000 | **$41.71** | **$41,710** | **$47,967** |

The one-unit estimate includes manual assembly setup but excludes minimum reel
buys, shipping, duties, tax, and the tools needed to program or measure the
unit. A realistic one-off purchasing budget is $250-$600 once those costs are
included.

The panel, radio module, Qi receiver, custom battery pack, and mechanical
integration dominate volume cost. The following non-recurring expenses are not
in per-unit COGS:

- Electrical and mechanical EVT lots, test fixtures, and destructive samples:
  approximately $3,000-$15,000.
- Rear-cover, spacer, adhesive, and assembly tooling: approximately
  $2,000-$20,000, depending on laser-cut parts versus molded tooling.
- Finished-product EMC, radio-exposure, Bluetooth, wireless-power,
  battery-safety, environmental, and market-specific compliance:
  approximately $25,000-$100,000 or more.
- MFi program, licensed component, audit, and certification charges if the
  product uses Apple's MagSafe marks or licensed features.

Obtain supplier quotations and compliance-lab scopes before treating the
100-unit or 1,000-unit totals as a purchase order budget.

## Reliability checklist

- BQ51013C receiver followed by a BQ25185 charger and SYS power path.
- 40 mA charge limit, 100 mA input limit, separate cell and coil NTCs, and
  charger fault decoding.
- Protected battery pack with a keyed, polarized three-wire harness.
- 47 uF on SYS and 100 uF on PANEL_3V0, each checked against regulator
  capacitance limits and qualified at operating DC bias.
- Module antenna flush with the board edge and an all-layer copper keep-out.
- UICR `REGOUT0=3.0 V` provisioning and a fail-closed check before GPIO setup.
- SWD test pads for brick recovery, since there is no USB port to fall back to.
- Signed, power-fail-safe DFU with trial boot, rollback, and monotonic version
  policy before field updates are enabled.
- Exact frame-length, bounds, alignment, CRC, and replay checks before a panel
  refresh.
- Busy timeout, watchdog, brownout logging, and forced periodic full refresh.
- Structural spacer, strain relief, cell swelling clearance, and electrical
  insulation under the rear cover.
- No refresh outside the panel's qualified 0-50 degrees Celsius range.

### EVT and DVT release matrix

The following checks need recorded measurements, instrument setup, sample size,
and raw data. A pass on one prototype is not a production qualification.

| Area | Initial acceptance criterion |
|---|---|
| Charger | 36-44 mA fast charge at 25 degrees Celsius; 4.2 V regulation within the BQ25185 limit; no charge outside the qualified pack temperature range |
| Power path | No reset or BQ25185 latch-off during receiver attach, detach, a full refresh, or a simultaneous BLE transfer |
| Panel rail | PANEL_3V0 stays within the TPS7A2030P tolerance during the measured 120 mA peak profile; no overshoot beyond the panel rating |
| Battery margin | BAT and SYS stay above the refresh floor at cold temperature, minimum allowed state of charge, aged-cell impedance, and worst-case radio timing |
| Panel high voltage | VGH, VGL, VSH1, VSH2, VSL, and VCOM match the panel waveform settings without overshoot or oscillation |
| Qi tuning | Measured `Ls`, `Ls'`, Q, series resonance, parallel resonance, current limit, and FOD calibration are archived for the final stack |
| Qi interoperability | Charge starts, regulates, terminates, and recovers on the WPC interoperability set at centered and allowed offset positions |
| Thermals | Cell stays within its charge specification; coil, receiver, charger, panel circuit, cover, and adhesive stay below their qualified limits |
| Sleep current | Connected-idle and disconnected-advertising current support the stated 60-90 day target at cell end of life |
| BLE | A full 48 KB frame completes within the foreground target and resumes after forced disconnects without corruption or stale-frame acceptance |
| RF | Throughput, packet error rate, and reconnect behavior pass attached and detached on every supported phone and case |
| Firmware update | Signed update, interrupted download, power loss during swap, failed trial image, rollback, stale version, lost owner, and SWD erase recovery all pass |
| Magnet assembly | Polarity and flux map pass incoming inspection; pull force is 650-900 gf; the tile does not rotate into the camera area |
| Mechanical | Panel bond, FPC, coil and NTC leads, cell carrier, rear cover, and SWD access pass drop, torsion, peel, sweat, thermal-cycle, and aging tests |
| Manufacturing | AOI/X-ray criteria, programming, rail tests, radio test, panel test image, current signature, serialized result record, and failed-unit quarantine are defined |

## Regulatory and MFi

- **"MagSafe" is Apple's mark.** Use generic compatibility language unless
  Apple approves the product through MFi. MFi controls licensed marks,
  accessory magnet specifications, approved sources, and any licensed
  electronic features.
- The public Apple accessory-array requirements call for N48H magnets,
  controlled polarity and flux, 7-13 um NiCuNi plating, coplanarity, a DC
  shield, and 650-900 gf pull force. Qualify camera OIS, autofocus, compass,
  magnetic-stripe-card, and wireless-charging interference.
- The Raytac modular approvals reduce radio test scope only when the host
  design follows every grant condition. The finished product still needs host
  labeling, RF exposure assessment, emissions testing, and the applicable FCC,
  ISED, CE, UKCA, MIC, KC, and SRRC filings for its sale regions.
- Complete the Bluetooth SIG qualification and product listing for the final
  firmware and GATT design.
- The receive-only Qi circuit is not a 15 W MagSafe transmitter. WPC
  certification is required to use Qi marks and is the best way to verify
  transmitter interoperability, FOD behavior, and thermal limits.
- Require a UN 38.3 test summary for the shipped pack and complete the
  applicable IEC 62133-2, UL 2054, shipping, recycling, RoHS, and REACH work.

## Decisions taken since 0.1.0 draft

- **The phone is the sole source of frames.** No Worker, no server push. This
  keeps the system to one radio and one trust boundary, at the cost of sub-minute
  remote updates (see BLE background).
- **Mono panel.** Black/white only. Grayscale or color is a later variant.
- **3.97-inch 480 x 800 panel on the nRF52833.** Largest mono e-paper that fits a
  6.1" Pro in **both** width and height with the ring high (camera-clear). The
  4.26" was tried and dropped — it overhangs the bottom of a 15 Pro by ~4 mm.
  Minis are dropped (too narrow). The 48 KB frame is why the MCU is the 128 KB
  nRF52833.
- **Pre-certified module, not bare QFN.** The nRF52833 ships as a Raytac
  MDBT50Q-512K module: it folds in the antenna, 32 MHz crystal, DC/DC, and RF
  match with modular certification. The module still requires its host
  keep-out, layout review, and finished-product tests.
- **Launch faces:** clock, calendar, weather, health, photo/image, custom text,
  and a best-effort notification summary. Transit is deferred.
- **Relaxed background cadence.** Target the iOS `BGTask` rhythm (roughly every
  15 to 30 minutes, adaptive), which is the best-battery choice; foreground
  updates are immediate. No tight always-on connection interval.
- **Push gap accepted, path reserved.** Phone-only for launch. The
  notification-summary face is the one that would justify an optional companion
  push service later, so the firmware and app are structured to add it without a
  redesign.
- **Charging is detach-and-drop on a Qi-compatible pad.** A BQ51013C receiver
  feeds a BQ25185 power-path charger. No pass-through stage is included.
- **No user connector.** Wireless charge, planned signed BLE DFU, and SWD pads
  for factory programming and full-erase recovery. USB-C was considered and
  dropped, subject to recovery testing.
- **Magnet-only retention.** The N48H accessory ring and DC shield follow the
  Apple accessory-array geometry. Pull force, rotation, camera, compass, card,
  and charging interference remain physical acceptance tests.
- **A later push service stays independent.** If the reserved notification path
  is built, it is a private companion service, not the [`inkbot/`](../inkbot/)
  Worker and it shares no code with it. The tile firmware and app stay agnostic
  to the sender.
- **Reference-design-based KiCad schematic.** Raytac MDBT50Q-512K module,
  BQ51013C receiver, BQ25185 charger, TPS7A2030P panel rail, complete SSD1677
  boost circuit, and a 0.8 mm board with a rounded battery cutout. Project under
  [`inkbot-magsafe/kicad/`](../inkbot-magsafe/kicad/).

The firmware and hardware scaffold live in
[`../inkbot-magsafe/`](../inkbot-magsafe/); the iOS app is deferred until they
are dialed in.

## Open questions

- Final spacer, adhesive, rear-cover materials, and the cell swelling budget.
- Whether a ring-only build has enough rotational stability or needs the
  optional orientation magnet.
- Qualified battery supplier, custom harness drawing, and measured pulse-current
  acceptance limit.
- Per-face `BGTask` cadence tuning: which faces (weather, health) warrant a
  `BGProcessingTask` versus a lighter `BGAppRefreshTask`, within the relaxed
  target?
