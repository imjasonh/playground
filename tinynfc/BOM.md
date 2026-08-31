# TinyNFC bill of materials

Cost estimates for **10**, **50**, and **100** assembled boards (buttons),
priced around August 2026. Primary path is [JLCPCB](https://jlcpcb.com/) fab +
SMT with parts from [LCSC](https://www.lcsc.com/) / JLCPCB Basic & Extended
libraries. DigiKey and Mouser links are included where the same MPNs are
stocked for Western one-offs or reorders.

Prices move. Re-quote before you order.

## Assumptions

| Item | Choice |
|------|--------|
| Board | Ø 24.26 mm round (US quarter), 2-layer, **1.6 mm** FR-4, ENIG (QFN-friendly) |
| Assembly | JLCPCB SMT, one side (Economic ≤30 pcs; Standard above that) |
| Component overage | ~10–20% attrition (see per-qty tables) |
| Currency | USD |
| Not included | Tax/VAT, firmware programming labor, stickers/enclosure, NRE beyond fab |

Antenna copper is on the PCB (no discrete inductor to buy).

**Thickness:** the bare board is **1.6 mm**. The 9×9 piezo sits about **1.8 mm**
tall on top, so the assembled stack is roughly **3.4 mm** at its thickest point.
JLCPCB also offers **0.8 mm** FR-4 if you want a flatter button (same outline;
re-quote).

## Quick compare (assembled + shipped)

| Qty | Lot total | Per unit | Notes |
|----:|----------:|---------:|-------|
| 10 | **~$130** | **~$13** | Prototype / give-away handful. Setup and shipping dominate. |
| 50 | **~$255** | **~$5.10** | Small batch; Standard SMT once you leave Economic's ≤30 limit. |
| 100 | **~$365** | **~$3.65** | Volume sweet spot in this estimate. |

Rounded mental math: tens of dollars each at 10, about five bucks at 50, under
four at 100.

## Parts

Unit prices are LCSC/JLCPCB-class breaks at each qty. Extended (line total)
multiplies by the overage count for that run.

| Ref | MPN / value | Pkg | @10 | @50 | @100 | Buy |
|-----|-------------|-----|----:|----:|-----:|-----|
| U1 | [NT3H2111W0FHKH](https://www.lcsc.com/product-detail/C710403.html) | XQFN-8 | $0.70 | $0.60 | $0.54 | [LCSC](https://www.lcsc.com/product-detail/C710403.html) · [DigiKey](https://www.digikey.com/en/products/filter/rfid-rf-access-monitoring-ics/895?s=NT3H2111W0FHKH) · [Mouser](https://www.mouser.com/c/?q=NT3H2111W0FHKH) |
| U2 | [ATTINY816-MNR](https://jlcpcb.com/partdetail/MicrochipTech-ATTINY816MNR/C2052778) | VQFN-20 | $0.60 | $0.50 | $0.45 | [JLCPCB](https://jlcpcb.com/partdetail/MicrochipTech-ATTINY816MNR/C2052778) · [DigiKey](https://www.digikey.com/en/products/detail/microchip-technology/ATTINY816-MNR/7387438) · [Mouser](https://www.mouser.com/ProductDetail/Microchip-Technology/ATTINY816-MNR) |
| PZ1 | [FUET-9018](https://www.lcsc.com/product-detail/Buzzers_FUET-FUET-9018_C391035.html) | 9×9 SMD | $0.42 | $0.37 | $0.31 | [LCSC](https://www.lcsc.com/product-detail/Buzzers_FUET-FUET-9018_C391035.html) · [JLCPCB](https://jlcpcb.com/partdetail/FUET-FUET9018/C391035) |
| Q1 | [DMP21D0UFB4-7B](https://www.lcsc.com/product-detail/C155329.html) | DFN1006-3 | $0.08 | $0.06 | $0.05 | [LCSC](https://www.lcsc.com/product-detail/C155329.html) · [DigiKey](https://www.digikey.com/en/products/filter/transistors-fets-mosfets-single/278?s=DMP21D0UFB4) |
| D1 | [TPESD8L3.3CT5G](https://www.lcsc.com/product-detail/C2830293.html) | 0402 TVS | $0.04 | $0.03 | $0.025 | [LCSC](https://www.lcsc.com/product-detail/C2830293.html) · [JLCPCB](https://jlcpcb.com/partdetail/TECHPUBLIC-TPESD8L33CT5G/C2830293) |
| C1 | 1.5 pF C0G ±0.1 pF | 0402 | $0.04 | $0.03 | $0.02 | [LCSC 0402 C0G](https://www.lcsc.com/products/Multilayer-Ceramic-Capacitors-MLCC-SMD-SMT_11222.html?keyword=1.5pF%200402) |
| C2 | 100 nF X7R 16 V | 0402 | $0.02 | $0.015 | $0.01 | [LCSC 100nF 0402](https://www.lcsc.com/products/Multilayer-Ceramic-Capacitors-MLCC-SMD-SMT_11222.html?keyword=100nF%200402) |
| C3 | 10 µF X5R ≥6.3 V | 0402 | $0.06 | $0.05 | $0.04 | [LCSC 10uF 0402](https://www.lcsc.com/products/Multilayer-Ceramic-Capacitors-MLCC-SMD-SMT_11222.html?keyword=10uF%200402) |
| R1 | 100 kΩ 1% | 0402 | $0.01 | $0.008 | $0.005 | [LCSC 100k 0402](https://www.lcsc.com/products/Chip-Resistor-Surface-Mount_11729.html?keyword=100k%200402) |
| R2 | 2.2 kΩ 1% | 0402 | $0.01 | $0.008 | $0.005 | [LCSC 2.2k 0402](https://www.lcsc.com/products/Chip-Resistor-Surface-Mount_11729.html?keyword=2.2k%200402) |
| R3 | 220 Ω 1% | 0402 | $0.01 | $0.008 | $0.005 | [LCSC 220R 0402](https://www.lcsc.com/products/Chip-Resistor-Surface-Mount_11729.html?keyword=220R%200402) |
| | **Unit BOM (1 set)** | | **~$1.99** | **~$1.68** | **~$1.46** | |

Piezo drop-in alternate: Murata
[PKMCS0909E4000-R1](https://www.lcsc.com/product-detail/C910763.html)
(same 9×9 land; ~2× the FUET price). The old 12×12 Murata `PKLCS1212E` is
louder but blocks the postage-stamp outline.

### Component line totals (with overage)

| Qty good | Order each SMT | Components total | Per good board |
|---------:|---------------:|-----------------:|---------------:|
| 10 | 12 | **~$24** | $2.40 |
| 50 | 55 | **~$92** | $1.85 |
| 100 | 105 | **~$153** | $1.53 |

## PCB and assembly

| Line | 10 | 50 | 100 | Notes |
|------|---:|---:|----:|-------|
| Bare PCB, Ø 24.26 mm, 2L ENIG | $8 ($0.80/ea) | $22 ($0.44/ea) | $35 ($0.35/ea) | [JLCPCB quote](https://cart.jlcpcb.com/quote). Round outline; HASL is cheaper; ENIG is safer for the VQFN. |
| SMT stencil | $7 | $7 | $7 | Usually once per design. |
| SMT assembly | $55 | $90 | $120 | Setup + place ~11 parts. Economic for ≤30; Standard for 50/100. Extended-part load fees included in the ballpark. |
| Intl. shipping (DHL-class) | $35 | $45 | $50 | To US/EU; economy sea is less. |
| **Fab + ship** | **~$105** | **~$164** | **~$212** | |

## Totals by quantity

### 10 boards

| | Total | Per unit |
|--|------:|---------:|
| Components only (12 sets) | $24 | $2.40 |
| Components + bare PCB | $32 | $3.20 |
| **Assembled + shipped** | **~$130** | **~$13** |

### 50 boards

| | Total | Per unit |
|--|------:|---------:|
| Components only (55 sets) | $92 | $1.85 |
| Components + bare PCB | $114 | $2.28 |
| **Assembled + shipped** | **~$255** | **~$5.10** |

### 100 boards

| | Total | Per unit |
|--|------:|---------:|
| Components only (105 sets) | $153 | $1.53 |
| Components + bare PCB | $188 | $1.88 |
| **Assembled + shipped** | **~$365** | **~$3.65** |

### Cost share at 100 (assembled run)

| Bucket | Share |
|--------|------:|
| Piezo (PZ1) | ~9% |
| NTAG + MCU | ~28% |
| Other parts | ~5% |
| PCB + stencil | ~11% |
| SMT labor | ~33% |
| Shipping | ~14% |

At 10, shipping + SMT setup eat most of the per-unit price; parts are a small
slice. That flips as qty climbs.

## Antenna note

A Ø 24.26 mm (US quarter) board with a Ø 23 mm circular spiral (5 turns, inner
clear ~Ø 16.7 mm) is enough to *target* ~2.75 µH after C1 trim, but harvested
current scales with coupling area. Phones with weak or offset NFC coils may
need a larger outline. Treat the quarter disc as the minimum to try first;
enlarge only if bench measurements say the rail collapses under piezo load.

## What this leaves out

- Bench programming (UPDI) and melody load.
- Failures beyond the overage (rework, antenna tune misses).
- Stickers, packaging, or a plastic case.
- Tariffs and VAT at the destination.
- Exact Extended-part load fees (they move with JLCPCB's catalog).
