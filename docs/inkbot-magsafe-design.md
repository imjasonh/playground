# Design: inkbot-magsafe, a MagSafe e-ink tile

> **Status: 0.8.0 EVT design, not yet built.** A 4-inch mono e-ink tile
> that snaps to the MagSafe ring on the back of an iPhone. The paired iPhone is
> the only source of frames; an iOS app pushes them over Bluetooth Low Energy
> (BLE), on demand or in the background. It runs off a tiny lithium-polymer
> (LiPo) cell and recharges after removal from the phone on a qualified Qi
> transmitter. This doc is the circuit, the bill of materials (BOM), and
> the pricing. The companion BOM lives in
> [`inkbot-magsafe-bom.csv`](inkbot-magsafe-bom.csv).

This is a sibling to the existing [`inkbot-esp32/`](../inkbot-esp32/) firmware.
That device is a tethered 7.5-inch panel that joins Wi-Fi and polls the
[`inkbot/`](../inkbot/) Worker. This one drops Wi-Fi, the wall wart, and the
Worker: it is battery-first, phone-first, and talks BLE to a phone in your
pocket. The phone composes every frame.

## What the brief gets right, and the one thing it gets wrong

The first-order battery model supports a 100 mAh starting point. A 4-inch mono
panel draws microamps while asleep and spends a few hundredths of a
milliamp-hour per modeled refresh. EVT must replace those assumptions with
measured current profiles and cold, aged-cell impedance.

The wrong assumption is the power source. **An iPhone does not send Qi power out
its back to an accessory stuck on the MagSafe ring.** Reverse wireless charging
to arbitrary accessories is not a feature Apple ships (the MagSafe Battery Pack
is a special case with its own handshake). So "infinite power whenever the phone
is picked up or set down" is not real. The tile runs on its own cell whenever it
is on the phone, on or off a charger.

### How it charges: detach and drop it on a pad

The tile carries a 2 W-rated Qi receive (RX) coil and limits nominal receiver
current to about 250 mA. Its accessory magnets hold it to the phone and align it
on a charger. To recharge, remove the tile from the phone and set it on a
qualified Qi pad. The supported transmitter set remains an EVT result, not a
universal compatibility claim.

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

## Decisions (locked for 0.8.0)

| Topic | Decision |
|-------|----------|
| MCU / radio | **Raytac MDBT50Q-1MV2**, a pre-certified nRF52840 module with 1 MiB flash, 256 KiB RAM, an integrated antenna, a 32 MHz crystal, DC/DC, and RF matching |
| Panel | **GDEY0397T81P**, 3.97-inch 480 x 800 portrait monochrome e-paper, SSD1677, partial refresh |
| Orientation | portrait; ring high on the tile, panel fills the tile and overlaps the ring |
| Battery | **LP242030 custom pack requirement**, 100 mAh, protected, at least 200 mA continuous pack discharge, 10 kOhm NTC, keyed three-wire harness, up to 3.5 mm thick |
| Power | **BQ51013C** Qi 1.3 receiver into a default-off **BQ25186** charger with a SYS power path |
| MCU power | **TPS7A0230P** 3.0 V nanopower LDO; nRF52840 VDD and VDDH tied for normal-voltage mode |
| Panel power | **TPS7A2030P** 3.0 V LDO, disabled with active discharge between refreshes |
| Charging | Qi 1.3 receiver configured for about 250 mA nominal and 300 mA hardware limit; no pass-through |
| Frame source | the paired iPhone only; no Worker, no second radio |
| Port | none; SWD test pads for factory flash and recovery. USB-C considered and dropped |
| Enclosure | panel front face, structural spacer, electrical insulation, and a flame-retardant rear cover |
| Magnets | Apple accessory-array geometry, N48H ring, low-carbon-steel DC shield, and a mandatory anti-rotation feature; final geometry is unresolved |
| Link | BLE 4.2+ GATT for control, **L2CAP connection-oriented channel** for the frame blob |
| iOS delivery | deferred until hardware is dialed in; Core Bluetooth central when built |
| Schematic | KiCad project under [`inkbot-magsafe/kicad/`](../inkbot-magsafe/kicad/) |

### Why nRF52840, not the ESP32-C3 or nRF52833

The brief names an ESP32-C3. It works, and it is cheap, but it is the wrong tool
for a battery-first BLE peripheral that must stay reachable in the background:

- **Deep sleep is not the interesting number; connected idle is.** To catch a
  background push, the tile has to hold a BLE connection or advertise. On the
  nRF52 a maintained connection with slave latency averages roughly 10–30 µA.
  The ESP32-C3 keeps its radio state in light sleep, not deep sleep, and connected
  light-sleep current is an order of magnitude higher.
- **The Nordic SoftDevice is a mature, qualified BLE stack** with good long-lived
  connection behavior; the e-ink hobbyist and product world runs on it.
- **A nanopower LDO isolates the MCU rail.** TPS7A0230P regulates SYS to 3.0 V.
  Tying VDD and VDDH follows the nRF52840 normal-voltage reference circuit and
  provides a valid rail for the BQ25186 I2C pull-ups.

The 3.97-inch panel needs a **48 KB mono framebuffer**. An nRF52833 has enough
RAM for one frame, but its 512 KiB flash cannot comfortably hold S113, equal
application and update slots, a signed bootloader, bond data, and two complete
frame slots. The **nRF52840** provides 1 MiB flash and 256 KiB RAM in the same
host footprint. The additional flash preserves the last committed frame while
a new frame or firmware image is written, so power loss does not destroy the
only recoverable copy.

The nRF52840 ships as the **pre-certified Raytac MDBT50Q-1MV2 module**, not a
bare QFN. The module integrates the 2.4 GHz antenna, the 32 MHz crystal, the
DC/DC inductors, and the RF matching network. It carries FCC and ISED modular
approvals plus supplier reports or declarations for CE, MIC, KC, SRRC, NCC, and
RCM. The module removes the board-side antenna matching network, but it does
not remove RF integration work. The PCB
keeps copper out beneath the antenna, places the antenna end at the board edge,
and still needs finished-product emissions and radiated-performance tests with
the phone, magnets, and coil installed. The module is about 2.05 mm tall. The
board adds a 10 uF MCU-rail capacitor and a 32.768 kHz crystal on P0.00/P0.01.
The NFCT pins stay unused.

## Block diagram

```
   WR222230 coil -> BQ51013C -> QI_OUT -> BQ25186 -> SYS
         |              |                    ^          |
      coil NTC       resonance/FOD           |          +-> 47 uF reservoir
                                             |
   protected LP242030 high-rate pack + NTC -> BAT---+

   SYS -> TPS7A0230P 3.0 V -> MDBT50Q VDD + VDDH
   SYS -> TPS7A2030P 3.0 V -> 100 uF -> SSD1677 panel power and boost circuit
   MDBT50Q-1MV2 <-> panel SPI, BUSY, reset, and panel-power enable
   MDBT50Q-1MV2 <-> BQ25186 I2C; default-off /CE gate; Qi EPT controls

   Factory and recovery: SWDIO, SWDCLK, reset, VDD reference, SYS, and ground
```

Signal notes: the panel is a bare chip-on-glass (COG) module on a 24-pin 0.5 mm
flex (FPC); its on-glass charge pump makes its own gate and source rails from
3.0 V. The board implements the panel data sheet's external MOSFET, inductor,
diodes, sense resistor, and reservoir capacitors. The TPS7A2030P disables and
actively discharges the panel rail between refreshes.

The 4.7 uF switched and high-voltage panel reservoirs use 35 V-rated 0805 X7R
parts, and the 1 uF reservoirs use 50 V-rated parts. EVT must verify effective
capacitance at DC bias and capture overshoot on every generated rail.

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
only the glass is shorter. A 480×800 mono frame is still **48 KB**. The
nRF52840 has room for the runtime framebuffer and two nonvolatile frame slots.

## Power budget

Assume the tile is off its charger for 24 hours, holds a background BLE
connection, and does 24 refreshes.

| Draw | Current / cost | Per day | Notes |
|---|---|---|---|
| nRF connected idle (360-375 ms interval, latency 4) | ~20 uA average | ~0.48 mAh | Effective maximum event spacing is 1.875 s; verify on supported phones |
| BQ25186 in battery-only mode | ~4 uA typical | ~0.10 mAh | Charger data-sheet value |
| TPS7A0230P MCU LDO | ~0.025 uA typical | <0.01 mAh | Verify the complete rail leakage |
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
exceeding the BQ25186's 100 uF maximum, and C27 adds 100 uF at the panel within
the TPS7A20's 200 uF stability limit. Those parts do not prove margin. EVT must
capture BAT, SYS, PANEL_3V0, and current at room temperature, cold temperature,
end-of-charge, and the refresh floor. The LP242030 cell specification permits
200 mA maximum discharge, but its reference PCM does not provide the required
continuous margin. Release `IMJ-BAT-001` only after the cell and custom PCM both
support the measured combined panel and radio pulse.

## Circuit design

### Power path

The **BQ51013C** Qi receiver supplies 5 V to a **BQ25186** charger and
power-path manager. The BQ25186 separates `BAT` from `SYS`, blocks reverse
drain into the receiver, and supplements a weak input from the cell. The
host-tested register plan sets 4.2 V regulation, a 100 mA input limit, 40 mA
fast charge, the IC's minimum 500 mA battery OCP threshold, and a 0-45 degrees
Celsius charge window. Target firmware must write and read back those values
before enabling charge. R5 and Q2 hold `/CE` high until configuration succeeds,
so reset or firmware failure leaves charging off rather than using the
charger's 60 degrees Celsius default limit. The 500 mA IC threshold does not
replace a pack-level PCM qualified for the cell's 200 mA continuous limit.

`STAT0.TS_OPEN_STAT` also asserts when the battery is below `VBAT_HALT`.
Firmware therefore reports that state as an ambiguous thermistor-open or
deeply discharged battery condition and keeps charging disabled. EVT must
define and test a TI-reviewed recovery path that does not bypass an open pack
thermistor.

There is no USB-C port on the shipping tile (see the next section).

The **TPS7A0230P** regulates SYS to `MCU_3V0`. The rail powers the Raytac
module's VDD and VDDH pins together in normal-voltage mode. A **TPS7A2030P**
creates the separate panel 3.0 V supply and actively discharges that rail while
disabled.

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

The MCU drives BQ51013C EN1 and EN2. After the BQ25186 reports charge complete,
firmware drives both high so the receiver sends charge-complete EPT 0x01 and
the transmitter can enter its low-power ping cycle. Returning both pins low
allows recharge. Overnight full-battery temperature and transmitter behavior
remain EVT gates.

### Ports: none, by design

Ship the tile with **no user connector.** Charging is wireless, and the planned
signed DFU transport uses BLE. This choice is valid only after the bootloader,
owner-recovery flow, and update rollback tests pass.

The reliability backstop is a set of **SWD test pads** (SWDIO, SWDCLK, GND, VDD)
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
inner copper. In1.Cu distributes SYS around three low-speed charger-control
tracks, and In2.Cu remains solid ground. The routed
34 x 23 mm battery cutout has 1 mm corner radii. Standard vias are
0.5/0.25 mm, minimum trace and signal clearance are 0.10 mm, and two Qi
receiver fanouts use 0.45/0.20 mm vias. Copper stays 0.5 mm from every routed
edge. The selected fabricator lists these values within its standard multilayer
process, but the fabrication drawing and quote remain release gates.

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
| Module | **~4.12 mm** |
| Protected battery pack in the cutout | **~4.77 mm** |
| Magnet ring plus DC shield | **~3.27 mm** |
| Coil, ferrite, and stacked film NTC | **~3.44 mm** |

The battery pack sets the baseline thickness. Adhesive tolerance, connector
clearance, cell swelling, and cosmetic films still need a mechanical tolerance
stack. A center orientation magnet can add thickness where it overlaps the
cell. The current sketch does overlap the cell and has been removed. A safe,
mandatory anti-rotation geometry remains a mechanical release blocker.

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
In1.Cu SYS distribution and the In2.Cu ground plane. Three locked, low-speed
charger-control tracks cross In1.Cu without cutting the ground plane. The flow
exports a Specctra DSN file, runs
Freerouting on F.Cu and B.Cu, imports the SES file, refills the planes, and
exports fabrication files. Every ground pad gets a via to In2.Cu; the outer
layers stay signal-only so disconnected pour islands cannot mask an open net.
`kicad/layout_route.py` contains the shared placement and fabrication rules.

Validate with `kicad/run_drc.py`, which calls KiCad's DRC engine through
pcbnew. `kicad/run_erc.py` checks the exact IC and connector pin contracts,
intentional no-connects, BOM coverage, and board-pad parity. Both checks must
pass on the release commit. They do not replace schematic review, DFM review,
or the bench validation table later in this document.

`production-gates.json` records each external review and physical qualification.
Every evidence path must resolve to a file inside `inkbot-magsafe/`. Normal
exports identify themselves as EVT in the fabrication manifest and record each
evidence file's size and SHA-256 digest. A production-labeled export fails
unless every gate has evidence, the classification is `PRODUCTION`, and the
source worktree is clean. The validator requires the complete ordered gate set,
so deleting or renaming a blocked gate cannot make the package releasable.

Recommended one-off sequence (validate function before optimizing thickness):

1. **Bench assembly.** Use an nRF52840 development kit, the
   GDEY0397T81P vendor adapter, and a current-limited bench supply. Prove the
   panel sequence, measured current profile, BLE transport, and failure
   recovery before connecting a cell.
2. **EVT lot.** Build at least five 0.8 mm, four-layer ENIG assemblies. Use the
   exact panel, coil, custom protected pack, and magnetic assembly in the BOM.
   Program firmware over the SWD fixture, then run the electrical and mechanical
   acceptance tests on every unit.

The Raytac module avoids a board-side RF matching network. It does not make the
finished product automatically compliant or guarantee range beside a phone.
Keep the module for production unless a later bare-QFN program budgets a new RF
layout, antenna tuning, and intentional-radiator certification.

### Phone compatibility and fit

The phone must have a compatible accessory magnet array, and the complete
60 x 99 mm assembly must clear its body, camera plateau, curved rear surface,
and case lip. The 30 mm ring-center offset is an EVT hypothesis. The
similarly named 30 mm limit in Apple's guidance applies to hosts that integrate
a MagSafe Charger Module, not as a universal camera rule for passive
accessories.

Do not publish a supported-phone table from body dimensions alone. Before DVT,
overlay the tolerance-controlled assembly on Apple's dimensional drawing for
each proposed phone. Include the model-specific camera keep-out, magnet center,
case geometry, lateral self-alignment error, rotation, cover thickness, and
manufacturing tolerance. Confirm positive hard-part clearance and camera
autofocus and stabilization behavior on physical phones and supported cases.
The 12 and 13 mini remain excluded because their 64.2 mm bodies are narrower
than the tile.

## BLE and iOS integration

The tile is a BLE peripheral (GATT server). The iOS app is the central. See the
[`ios/`](../ios/) app; this ships as a new experiment there rather than a new
top-level app.

### GATT layout

| Characteristic | Properties | Purpose |
|---|---|---|
| Control | encrypted write with response | begin frame, region, full-vs-partial, commit, and resume offset |
| Capabilities | encrypted read | protocol version, GATT chunk limit, optional LE PSM, and L2CAP chunk limit |
| Status | read / notify | SYS estimate, charge state, temperature availability, and last-refresh result |
| Frame fallback | encrypted write without response | chunked pixel data when L2CAP is unavailable |

The cell and coil NTCs terminate at their protection ICs and are not shared
with the MCU. A separate NCU18XH103F60RB thermistor sits beside the panel bond
line. P0.27 excites its 10 kOhm divider only during a sample, and P0.02/AIN0
measures the result against the ratiometric SAADC reference. Firmware treats an
open or shorted sensor as unavailable and blocks refresh. EVT must correlate
this board-edge reading with the glass temperature before freezing the limits.
The SSD1677 can still use its internal sensor for waveform selection.

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
not reopen the replay window. To reset ownership without a button or the old
phone, place and remove the tile from a Qi pad five times within 45 seconds.
Each attached and detached phase must last at least 750 ms, and the fifth
placement leaves the tile on external power for the erase. Host-tested gesture
logic rejects contact bounce and expired sequences, and it triggers only after
the fifth attached phase remains stable for 750 ms. Target firmware must still
erase both bond-journal copies and the prior owner's replay boundary, verify
the erases, and display a new random passkey before this recovery path is
complete. SWD full erase remains the factory fallback.

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

Protocol version 1 uses a fixed 24-byte header. It rejects unsupported versions,
nonzero reserved bytes, invalid or unaligned windows, mismatched lengths,
conflicting frame ids, stale ids, out-of-order chunks, and bad CRCs. A repeated
active header returns the received offset so a dropped transfer can resume.
Passing the CRC marks a frame as verified, but it does not advance the replay
boundary. Firmware advances that boundary only after atomically committing the
pixels and metadata to flash.

`src/wire.rs` fixes the service and characteristic UUIDs and the byte-level
messages that both implementations use. Control requests carry a version and
an opcode for begin, commit, cancel, or status. GATT fallback chunks carry the
frame id and required offset before nonempty pixel data. The 16-byte status
message reports phase, error code, active frame id, resume offset, and committed
frame id. The capabilities message publishes negotiated GATT and L2CAP limits
and the optional LE PSM. An inactive transfer expires after 30 seconds. Golden
vectors lock each encoding for the future Swift implementation.

The glass is mounted with its long axis vertical, but SSD1677 RAM remains
800 source pixels by 480 gate pixels. The iOS encoder rotates each portrait
face into that controller-native order before transfer. Frame windows use the
same 800 x 480 coordinates, with source-axis bounds aligned to whole bytes.
This keeps the device from needing a second 48 KB buffer for rotation.

On demand (app in foreground) is the easy case: connect, open the L2CAP channel,
stream, commit, done.

## Firmware

The Rust crate reserves flash and RAM for S113 7.3.0, which supports the
nRF52840 peripheral role, LE Secure Connections, 2M PHY, and L2CAP
connection-oriented channels with less flash than S140. The 1 MiB map allocates
112 KiB to the MBR and S113, equal 256 KiB application and update slots, a
16 KiB bond and settings journal, five wear-leveled 48 KiB frame slots,
separate frame and fault journals, and the top 128 KiB for the bootloader and
Nordic metadata.
The linker provisionally reserves 32 KiB of the 256 KiB RAM for S113 and rejects
an application load segment outside its primary slot.
At the nRF52840's 10,000-cycle minimum page endurance and 24 durable frames per
day, round-robin use of all five slots provides at least 2,083 days of modeled
frame-storage life. Target firmware must preserve that rotation and report
write or erase failures.
Host-tested code implements versioned frame validation, replay checks, a
separate durable-commit step, panel window rules, periodic full refresh policy,
charger policy, SYS conversion, voltage and temperature gates, the complete
flash map, and CRC-protected wear-leveled frame metadata. Final RAM origin must
come from `sd_ble_enable()` with the released connection settings.

The following target integrations remain release blockers:

- Configure panel power and charge disabled before all other GPIO.
- Start S113 from the external 32.768 kHz crystal and implement bonded GATT plus
  the L2CAP server.
- Configure the BQ25186 for 40 mA charge, 100 mA input, 500 mA IC battery OCP,
  4.2 V regulation, and a 0-45 degrees Celsius charge window before driving
  `CHG_ENABLE` high. Capture read-to-clear fault flags after live status.
- After final test and with Qi input absent, enter BQ25186 ship mode. Verify
  transport current and first-attachment wake behavior on every production
  unit.
- Stream incoming data to an atomic flash record and seed the replay boundary
  from its committed metadata after reset.
- Implement the SSD1677 reset, two-RAM initialization, temperature-selected
  waveform, BUSY timeout, full and partial refresh, deep sleep, and rail
  discharge sequence.
- Sample `SYS_SENSE`, retain reset and brownout causes, and run a watchdog that
  also covers stalled panel and radio operations. Treat SYS as a resting-cell
  estimate only when Qi input is absent.
- Add a signed, power-fail-safe bootloader with a trial boot, rollback, and
  monotonic version floor. Size its active, update, state, and S113 partitions
  from the final linked image.
- Lock production debug against readout while preserving documented full-erase
  recovery through CTRL-AP and the SWD fixture.
- Program and verify both UICR `PSELRESET` words for P0.18 in the factory image
  so the reset pogo pad works before field recovery is needed.
- Connect the five-attachment owner-reset gesture to verified bond erasure and
  new-passkey display while the tile remains on Qi power.

BLE transports firmware from the phone. A CRC-only frame path and an unsigned
image are not acceptable DFU mechanisms.

## Bill of materials and cost

Full line items with part numbers and price columns are in
[`inkbot-magsafe-bom.csv`](inkbot-magsafe-bom.csv). The modeled direct build
cost includes parts, PCB fabrication, SMT, final integration, programming,
end-of-line test, spacer, insulation, and rear cover. Each CSV price is the
extended cost for every reference in that row, not a single component price:

| Quantity | Unit direct cost | Build total | With 15% procurement contingency |
|---:|---:|---:|---:|
| 1 | **$173.65** | **$174** | **$200** |
| 100 | **$63.05** | **$6,305** | **$7,251** |
| 1,000 | **$44.22** | **$44,220** | **$50,853** |

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

- BQ51013C receiver followed by a default-off BQ25186 charger and SYS power
  path.
- Required 40 mA charge, 100 mA input, 500 mA IC battery OCP, 0-45 degrees
  Celsius JEITA limits, separate cell and coil NTCs, and charger fault decoding.
- Protected high-rate battery pack with a keyed, polarized three-wire harness
  and at least 200 mA continuous pack-level discharge capability.
- 47 uF on SYS and 100 uF on PANEL_3V0, each checked against regulator
  capacitance limits and qualified at operating DC bias.
- Module antenna flush with the board edge and an all-layer copper keep-out.
- TPS7A0230P MCU rail with VDD and VDDH tied for normal-voltage operation.
- SWD test pads for brick recovery, since there is no USB port to fall back to.
- Signed, power-fail-safe DFU with trial boot, rollback, and monotonic version
  policy before field updates are enabled.
- Exact frame-length, bounds, alignment, CRC, and replay checks before a panel
  refresh.
- Busy timeout, watchdog, brownout logging, and forced periodic full refresh.
- Duty-cycled, open- and short-detecting panel temperature measurement.
- No panel refresh while the Qi receiver reports power transfer.
- BQ25186 ship mode after final test, with measured shelf current and a verified
  wake on the first valid Qi attachment.
- Structural spacer, strain relief, cell swelling clearance, and electrical
  insulation under the rear cover.
- No refresh outside the panel's qualified 0-50 degrees Celsius range.

### EVT and DVT release matrix

The following checks need recorded measurements, instrument setup, sample size,
and raw data. A pass on one prototype is not a production qualification.

| Area | Initial acceptance criterion |
|---|---|
| Charger | 36-44 mA fast charge at 25 degrees Celsius; 4.2 V regulation within the BQ25186 limit; no charge outside 0-45 degrees Celsius; reset leaves charging disabled |
| Power path | No reset or BQ25186 latch-off during receiver attach, detach, a full refresh, or a simultaneous BLE transfer |
| Panel rail | PANEL_3V0 stays within the TPS7A2030P tolerance during the measured 120 mA peak profile; no overshoot beyond the panel rating |
| Battery margin | BAT and SYS stay above the refresh floor at cold temperature, minimum allowed state of charge, aged-cell impedance, and worst-case radio timing |
| Panel high voltage | VGH, VGL, VSH1, VSH2, VSL, and VCOM match the panel waveform settings without overshoot or oscillation |
| Qi tuning | Measured `Ls`, `Ls'`, Q, series resonance, parallel resonance, current limit, and FOD calibration are archived for the final stack |
| Qi interoperability | Charge starts, regulates, terminates, and recovers on the WPC interoperability set at centered and allowed offset positions; the accessory magnet array does not repel or displace the tile on supported magnetic chargers |
| Thermals | Cell stays within its charge specification; coil, receiver, charger, panel circuit, cover, and adhesive stay below their qualified limits |
| Sleep current | Connected-idle and disconnected-advertising current support the stated 60-90 day target at cell end of life |
| Shelf mode | A detached unit enters ship mode after final test, draws no more than the qualified transport-current limit, and wakes on its first valid Qi attachment |
| BLE | A full 48 KB frame completes within the foreground target and resumes after forced disconnects without corruption or stale-frame acceptance |
| RF | Throughput, packet error rate, and reconnect behavior pass attached and detached on every supported phone and case |
| Power-loss recovery | Forced resets at every flash erase, payload write, metadata commit, panel update, settings update, and DFU swap boundary retain the previous committed frame and a bootable signed image |
| Firmware update | Signed update, interrupted download, power loss during swap, failed trial image, rollback, stale version, lost owner, and SWD erase recovery all pass |
| Magnet assembly | Polarity and flux map pass incoming inspection; removal force meets the approved Apple procedure and the project's provisional 650-900 gf internal target; the tile does not rotate into the camera area |
| Mechanical | Panel bond, FPC, coil and NTC leads, cell carrier, rear cover, and SWD access pass drop, torsion, peel, sweat, thermal-cycle, and aging tests |
| Manufacturing | AOI/X-ray criteria, programming, rail tests, radio test, panel test image, current signature, serialized result record, and failed-unit quarantine are defined |
| Supply chain | The approved-vendor list records manufacturer part numbers, alternates, lifecycle status, minimum order quantities, lead times, incoming inspection, lot traceability, and capacity quotations for the production forecast |

## Regulatory and MFi

- **"MagSafe" is Apple's mark.** Use generic compatibility language unless
  Apple approves the product through MFi. MFi controls licensed marks,
  accessory magnet specifications, approved sources, and any licensed
  electronic features.
- The public Apple accessory-array material calls for N48H magnets, controlled
  polarity and flux, 7-13 um NiCuNi plating, coplanarity, and a DC shield.
  Confirm force limits and procedures through the current Apple program rather
  than treating the project's 650-900 gf target as a universal requirement.
  Qualify camera OIS, autofocus, compass, magnetic-stripe-card, and
  wireless-charging interference.
- The Raytac FCC and ISED modular approvals reduce radio test scope only when
  the host design follows every grant condition. The finished product still
  needs host labeling, RF exposure assessment, emissions testing, and the
  applicable FCC, ISED, CE, UKCA, MIC, KC, and SRRC filings for its sale
  regions.
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
- **3.97-inch 480 x 800 panel on the nRF52840.** Largest mono e-paper that fits a
  6.1" Pro in **both** width and height with the ring high (camera-clear). The
  4.26" was tried and dropped — it overhangs the bottom of a 15 Pro by ~4 mm.
  Minis are dropped because they are too narrow. The nRF52840 provides enough
  flash for equal update slots and five wear-leveled 48 KiB frame copies.
- **Pre-certified module, not bare QFN.** The nRF52840 ships as a Raytac
  MDBT50Q-1MV2 module with the antenna, 32 MHz crystal, DC/DC, and RF matching.
  The module still requires its host keep-out, layout review, and
  finished-product tests.
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
  feeds a BQ25186 power-path charger. No pass-through stage is included.
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
- **Reference-design-based KiCad schematic.** Raytac MDBT50Q-1MV2 module,
  BQ51013C receiver, BQ25186 charger, TPS7A0230P MCU rail, TPS7A2030P panel
  rail, complete SSD1677
  boost circuit, and a 0.8 mm board with a rounded battery cutout. Project under
  [`inkbot-magsafe/kicad/`](../inkbot-magsafe/kicad/).

The firmware and hardware scaffold live in
[`../inkbot-magsafe/`](../inkbot-magsafe/); the iOS app is deferred until they
are dialed in.

## Open questions

- Final spacer, adhesive, rear-cover materials, and the cell swelling budget.
- The anti-rotation geometry that meets Apple alignment requirements without
  loading the pouch cell or disrupting Qi coupling.
- Qualified battery supplier, custom harness drawing, and measured pulse-current
  acceptance limit.
- Per-face `BGTask` cadence tuning: which faces (weather, health) warrant a
  `BGProcessingTask` versus a lighter `BGAppRefreshTask`, within the relaxed
  target?
