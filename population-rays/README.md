# Population Rays

From a pin on the map: how far must a **100 ft** corridor go in each direction
before it hits **N** people?

Petal length = that distance. Short in Manhattan; long (or unreachable) in
Wyoming. At the packaged ~2 km grid, that thin corridor is treated as about
one cell wide so rays through cities like LA still count the people they
cross.

## Controls

- **People to hit** — target N (10k–500k)
- **Search** — US city or address (Nominatim; contiguous US only)
- Presets: Manhattan / Wyoming / My location
- 72 directions (every 5°); corridor width fixed at 100 ft

## Run

```bash
cd population-rays
npm start
npm test
```

## Data

Meta / CIESIN HRSL population counts:

| File | Resolution | Coverage |
|------|------------|----------|
| `data/conus-0p02.*` | ~2.2 km | Contiguous US |
| `data/northeast-0p005.*` | ~550 m | NYC metro |

Rebuild: `python3 scripts/build-population-grid.py`
