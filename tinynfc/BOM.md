# TinyNFC bill of materials

Cost estimate for **100 assembled boards** (buttons), priced around August 2026.
Primary path is [JLCPCB](https://jlcpcb.com/) fab + SMT with parts from
[LCSC](https://www.lcsc.com/) / JLCPCB Basic & Extended libraries. DigiKey and
Mouser links are included where the same MPNs are stocked for Western
one-offs or reorders.

Prices move. Re-quote before you order.

## Assumptions

| Item | Choice |
|------|--------|
| Quantity | 100 good boards |
| Component overage | Order 105 of each SMT part (~5% attrition) |
| Board | 28 mm × 28 mm, 2-layer, 1.6 mm FR-4, ENIG (QFN-friendly) |
| Assembly | JLCPCB Economic SMT, one side |
| Currency | USD |
| Not included | Shipping tax/VAT, firmware programming labor, stickers/enclosure, NRE beyond fab |

Antenna copper is on the PCB (no discrete inductor to buy).

## Parts (105 of each for 100 boards)

| Ref | MPN / value | Pkg | Unit @ ~100 | Ext (105) | Buy |
|-----|-------------|-----|-------------|-----------|-----|
| U1 | [NT3H2111W0FHKH](https://www.lcsc.com/product-detail/C710403.html) | XQFN-8 | $0.54 | $56.70 | [LCSC](https://www.lcsc.com/product-detail/C710403.html) · [DigiKey](https://www.digikey.com/en/products/filter/rfid-rf-access-monitoring-ics/895?s=NT3H2111W0FHKH) · [Mouser](https://www.mouser.com/c/?q=NT3H2111W0FHKH) |
| U2 | [ATTINY816-MNR](https://jlcpcb.com/partdetail/MicrochipTech-ATTINY816MNR/C2052778) | VQFN-20 | $0.45 | $47.25 | [JLCPCB](https://jlcpcb.com/partdetail/MicrochipTech-ATTINY816MNR/C2052778) · [DigiKey](https://www.digikey.com/en/products/detail/microchip-technology/ATTINY816-MNR/7387438) · [Mouser](https://www.mouser.com/ProductDetail/Microchip-Technology/ATTINY816-MNR) |
| PZ1 | [FUET-9018](https://www.lcsc.com/product-detail/Buzzers_FUET-FUET-9018_C391035.html) | 9×9 SMD | $0.31 | $32.55 | [LCSC](https://www.lcsc.com/product-detail/Buzzers_FUET-FUET-9018_C391035.html) · [JLCPCB](https://jlcpcb.com/partdetail/FUET-FUET9018/C391035) |
| Q1 | [DMP21D0UFB4-7B](https://www.lcsc.com/product-detail/C155329.html) | DFN1006-3 | $0.05 | $5.25 | [LCSC](https://www.lcsc.com/product-detail/C155329.html) · [DigiKey](https://www.digikey.com/en/products/filter/transistors-fets-mosfets-single/278?s=DMP21D0UFB4) |
| D1 | [TPESD8L3.3CT5G](https://www.lcsc.com/product-detail/C2830293.html) | 0402 TVS | $0.025 | $2.63 | [LCSC](https://www.lcsc.com/product-detail/C2830293.html) · [JLCPCB](https://jlcpcb.com/partdetail/TECHPUBLIC-TPESD8L33CT5G/C2830293) |
| C1 | 1.5 pF C0G ±0.1 pF | 0402 | $0.02 | $2.10 | [LCSC 0402 C0G](https://www.lcsc.com/products/Multilayer-Ceramic-Capacitors-MLCC-SMD-SMT_11222.html?keyword=1.5pF%200402) |
| C2 | 100 nF X7R 16 V | 0402 | $0.01 | $1.05 | [LCSC 100nF 0402](https://www.lcsc.com/products/Multilayer-Ceramic-Capacitors-MLCC-SMD-SMT_11222.html?keyword=100nF%200402) |
| C3 | 10 µF X5R ≥6.3 V | 0402 | $0.04 | $4.20 | [LCSC 10uF 0402](https://www.lcsc.com/products/Multilayer-Ceramic-Capacitors-MLCC-SMD-SMT_11222.html?keyword=10uF%200402) |
| R1 | 100 kΩ 1% | 0402 | $0.005 | $0.53 | [LCSC 100k 0402](https://www.lcsc.com/products/Chip-Resistor-Surface-Mount_11729.html?keyword=100k%200402) |
| R2 | 2.2 kΩ 1% | 0402 | $0.005 | $0.53 | [LCSC 2.2k 0402](https://www.lcsc.com/products/Chip-Resistor-Surface-Mount_11729.html?keyword=2.2k%200402) |
| R3 | 220 Ω 1% | 0402 | $0.005 | $0.53 | [LCSC 220R 0402](https://www.lcsc.com/products/Chip-Resistor-Surface-Mount_11729.html?keyword=220R%200402) |
| | | | **Components** | **~$153** | |

Piezo drop-in alternate: Murata
[PKMCS0909E4000-R1](https://www.lcsc.com/product-detail/C910763.html)
(~$0.69 @100, same 9×9 land). The old 12×12 Murata `PKLCS1212E` is louder but
blocks a postage-stamp outline and costs about twice as much at this qty.

## PCB and assembly (100 boards)

| Line | Estimate | Notes / quote |
|------|----------|---------------|
| Bare PCB, 100× 28×28 mm, 2L ENIG | $35 ($0.35/ea) | [JLCPCB quote](https://cart.jlcpcb.com/quote). Smaller than a business card; HASL is cheaper but ENIG is safer for the VQFN. |
| SMT stencil | $7 | Ordered with the PCB. |
| Economic SMT assembly | $120 ($1.20/ea) | Setup + place ~11 parts/side. Re-quote after Gerbers. |
| International shipping (DHL-class) | $50 | To US/EU; economy sea is less. |
| | **Fab + ship** | **~$212** |

## Totals for 100 buttons

| | Total | Per unit |
|--|------:|---------:|
| Components only (105 sets) | $153 | $1.53 |
| Components + bare PCB | $188 | $1.88 |
| **Assembled + shipped (recommended)** | **~$365** | **~$3.65** |

Rounded: plan on about **$3.70 per button** all-in for a 100-piece China SMT run, or about **$370** for the lot.

### Cost share (assembled run)

| Bucket | Share |
|--------|------:|
| Piezo (PZ1) | ~9% |
| NTAG + MCU | ~28% |
| Other parts | ~5% |
| PCB + stencil | ~11% |
| SMT labor | ~33% |
| Shipping | ~14% |

## Antenna note

A 28 mm board with a 23 mm spiral is enough to *target* ~2.75 µH with six
turns, but harvested current scales with coupling area. Phones with weak or
offset NFC coils may need a larger outline. Treat the postage-stamp size as the
minimum to try first; enlarge only if bench measurements say the rail collapses
under piezo load.

## What this leaves out

- Bench programming (UPDI) and melody load. Budget a few hours of your time, or a fixture later.
- Failures beyond the 5% part overage (rework, antenna tune misses).
- Stickers, packaging, or a plastic case.
- Tariffs and VAT at the destination.
