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
| Board | 40 mm × 40 mm, 2-layer, 1.6 mm FR-4, ENIG (QFN-friendly) |
| Assembly | JLCPCB Economic SMT, one side |
| Currency | USD |
| Not included | Shipping tax/VAT, firmware programming labor, stickers/enclosure, NRE beyond fab |

Antenna copper is on the PCB (no discrete inductor to buy).

## Parts (105 of each for 100 boards)

| Ref | MPN / value | Pkg | Unit @ ~100 | Ext (105) | Buy |
|-----|-------------|-----|-------------|-----------|-----|
| U1 | [NT3H2111W0FHKH](https://www.lcsc.com/product-detail/C710403.html) | XQFN-8 | $0.54 | $56.70 | [LCSC](https://www.lcsc.com/product-detail/C710403.html) · [DigiKey](https://www.digikey.com/en/products/filter/rfid-rf-access-monitoring-ics/895?s=NT3H2111W0FHKH) · [Mouser](https://www.mouser.com/c/?q=NT3H2111W0FHKH) |
| U2 | [ATTINY816-MNR](https://jlcpcb.com/partdetail/MicrochipTech-ATTINY816MNR/C2052778) | VQFN-20 | $0.45 | $47.25 | [JLCPCB](https://jlcpcb.com/partdetail/MicrochipTech-ATTINY816MNR/C2052778) · [DigiKey](https://www.digikey.com/en/products/detail/microchip-technology/ATTINY816-MNR/7387438) · [Mouser](https://www.mouser.com/ProductDetail/Microchip-Technology/ATTINY816-MNR) |
| PZ1 | [PKLCS1212E4001-R1](https://www.lcsc.com/product-detail/C113159.html) | 12×12 SMD | $0.72 | $75.60 | [LCSC](https://www.lcsc.com/product-detail/C113159.html) · [DigiKey](https://www.digikey.com/en/products/detail/murata-electronics/PKLCS1212E4001-R1/2530337) · [Mouser](https://www.mouser.com/ProductDetail/Murata-Electronics/PKLCS1212E4001-R1) |
| Q1 | [DMP21D0UFB4-7B](https://www.lcsc.com/product-detail/C155329.html) | DFN1006-3 | $0.05 | $5.25 | [LCSC](https://www.lcsc.com/product-detail/C155329.html) · [DigiKey](https://www.digikey.com/en/products/filter/transistors-fets-mosfets-single/278?s=DMP21D0UFB4) |
| D1 | [TPESD8L3.3CT5G](https://www.lcsc.com/product-detail/C2830293.html) | 0402 TVS | $0.025 | $2.63 | [LCSC](https://www.lcsc.com/product-detail/C2830293.html) · [JLCPCB](https://jlcpcb.com/partdetail/TECHPUBLIC-TPESD8L33CT5G/C2830293) |
| C1 | 1.5 pF C0G ±0.1 pF | 0402 | $0.02 | $2.10 | [LCSC 0402 C0G](https://www.lcsc.com/products/Multilayer-Ceramic-Capacitors-MLCC-SMD-SMT_11222.html?keyword=1.5pF%200402) |
| C2 | 100 nF X7R 16 V | 0402 | $0.01 | $1.05 | [LCSC 100nF 0402](https://www.lcsc.com/products/Multilayer-Ceramic-Capacitors-MLCC-SMD-SMT_11222.html?keyword=100nF%200402) |
| C3 | 10 µF X5R ≥6.3 V | 0402 | $0.04 | $4.20 | [LCSC 10uF 0402](https://www.lcsc.com/products/Multilayer-Ceramic-Capacitors-MLCC-SMD-SMT_11222.html?keyword=10uF%200402) |
| R1 | 100 kΩ 1% | 0402 | $0.005 | $0.53 | [LCSC 100k 0402](https://www.lcsc.com/products/Chip-Resistor-Surface-Mount_11729.html?keyword=100k%200402) |
| R2 | 2.2 kΩ 1% | 0402 | $0.005 | $0.53 | [LCSC 2.2k 0402](https://www.lcsc.com/products/Chip-Resistor-Surface-Mount_11729.html?keyword=2.2k%200402) |
| R3 | 220 Ω 1% | 0402 | $0.005 | $0.53 | [LCSC 220R 0402](https://www.lcsc.com/products/Chip-Resistor-Surface-Mount_11729.html?keyword=220R%200402) |
| | | | **Components** | **~$196** | |

Piezo dominates the BOM. Everything else is under a dollar combined at this qty.

## PCB and assembly (100 boards)

| Line | Estimate | Notes / quote |
|------|----------|---------------|
| Bare PCB, 100× 40×40 mm, 2L ENIG | $45 ($0.45/ea) | [JLCPCB quote](https://cart.jlcpcb.com/quote). HASL is cheaper (~$25–35) but ENIG is safer for the VQFN. |
| SMT stencil | $7 | Ordered with the PCB. |
| Economic SMT assembly | $120 ($1.20/ea) | Setup + place ~11 parts/side. Re-quote after Gerbers. |
| International shipping (DHL-class) | $50 | To US/EU; economy sea is less. |
| | **Fab + ship** | **~$222** |

## Totals for 100 buttons

| | Total | Per unit |
|--|------:|---------:|
| Components only (105 sets) | $196 | $1.96 |
| Components + bare PCB | $241 | $2.41 |
| **Assembled + shipped (recommended)** | **~$418** | **~$4.18** |

Rounded: plan on about **$4.20 per button** all-in for a 100-piece China SMT run, or about **$420** for the lot.

### Cost share (assembled run)

| Bucket | Share |
|--------|------:|
| Piezo (PZ1) | ~18% |
| NTAG + MCU | ~25% |
| Other parts | ~4% |
| PCB + stencil | ~12% |
| SMT labor | ~29% |
| Shipping | ~12% |

## What this leaves out

- Bench programming (UPDI) and melody load. Budget a few hours of your time, or a fixture later.
- Failures beyond the 5% part overage (rework, antenna tune misses).
- Stickers, packaging, or a plastic case.
- Tariffs and VAT at the destination.

## Cheaper / dearer knobs

- Drop ENIG to lead-free HASL if the fab’s QFN process is proven. Saves roughly $0.10–0.20 per board.
- Substitute a cheaper 12 mm piezo once you measure volume on NFC power. The Murata part is the single biggest component line.
- At 500+ boards, piezo and MCU reel pricing drop further; assembly per-unit falls faster than parts.

See also [`design.md`](design.md) and the KiCad project under [`kicad/`](kicad/).
