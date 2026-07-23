# Population Rays

From a pin on the map: simulate a corridor **M feet/miles wide** in every
direction. How far until that corridor hits **N** people?

Petal length = that distance. Short in Manhattan; often unreachable in Wyoming.

## Controls

- **Corridor width** — strip width (ft → mi)
- **People to hit** — target N
- Presets: Manhattan / Wyoming / My location
- 72 directions (every 5°)

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
