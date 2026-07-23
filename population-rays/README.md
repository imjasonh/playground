# Population Rays

From a pin on the map: how far must a **100 ft** corridor go in each direction
before it hits **N** people?

Petal length = that distance. Short in Manhattan (NY); longer from
Manhattan, KS or Manhattan, IL. At the packaged ~2 km grid, that thin
corridor is treated as about one cell wide. Samples on a grid line (common
for exact N/S/E/W) split credit across the two adjacent cells instead of
picking one side.

## Controls

- **People to hit** — target N (10k–500k)
- **Search** — US city or address (Nominatim; contiguous US only)
- Presets: Manhattan / Manhattan, KS / Manhattan, IL / My location
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

Each ray uses the finest covering grid that can hit N on its own; if the
metro tile cannot, it falls back to CONUS for that whole bearing (avoids
stitching a narrow fine strip to a wide coarse strip mid-ray).

Rebuild: `python3 scripts/build-population-grid.py`
