# Population Rays

From a pin on the map: how far must a filled **2°** pie slice go in each
direction before it hits **N** people?

Petal length = that distance. Short in Manhattan (NY); longer from
Manhattan, KS or Manhattan, IL. Each slice counts population cells whose
centers fall inside it (finest covering grid first, then CONUS beyond a
metro tile). Directions that still cannot hit N show as slate fans out to
the search limit, fading to transparent.

## Controls

- **People to hit** — target N (10k–500k)
- **Search** — US city or address (Nominatim; contiguous US only)
- Presets: Manhattan / Manhattan, KS / Manhattan, IL / My location
- 180 slices (every 2°); angular width matches the spacing so they tile 360°

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
