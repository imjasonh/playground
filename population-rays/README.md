# Population Rays

From any point in the contiguous US, visualize **how many people’s homes
intersect a thin corridor** in every direction — or **how far the corridor must
reach to hit N people**.

The classic Manhattan intuition: from Midtown, a 100′ strip running west crosses
far fewer homes than the same strip pointed southeast into Brooklyn.

## Idea

Treat “homes along a line” as a corridor of width **W** and length **L** in
bearing **D**. With gridded population density ρ, the count is the line integral

\[
\int_0^L \rho(s)\,W\,ds
\]

That formulation stays meaningful when **W** (e.g. 100 feet) is much thinner
than a grid cell: we count the *share* of each cell the strip covers, not whether
a cell centroid happens to fall inside the strip.

Two complementary modes:

1. **People within a distance** — fix L, plot people vs direction (rose petals
   scaled by count).
2. **Distance to reach N people** — fix a target (default 1M), plot how far each
   bearing must go.

## Data

Bundled grids are sum-aggregated from the
[Meta / CIESIN High Resolution Settlement Layer](https://registry.opendata.aws/dataforgood-fb-hrsl/)
(~30&nbsp;m population-count Cloud-Optimized GeoTIFFs on AWS Open Data, CC BY 4.0):

| File | Resolution | Coverage |
|------|------------|----------|
| `data/conus-0p02.*` | ~2.2 km (`0.02°`) | Contiguous US |
| `data/northeast-0p005.*` | ~550 m (`0.005°`) | NYC metro / Northeast |

Rebuild (needs GDAL + network access to the AWS bucket):

```bash
python3 scripts/build-population-grid.py
```

## Run locally

```bash
cd population-rays
npm start          # static server on :3000
npm test           # unit + data probes
```

Open the page, click the map (or drag the pin). Defaults start at Times Square.

## Project layout

```
population-rays/
├── index.html
├── styles.css
├── src/
│   ├── geo.js      # bearings / distances
│   ├── grid.js     # gzip float32 grid loader
│   ├── rays.js     # corridor integral + rose
│   └── app.js      # Leaflet UI
├── data/           # packaged population grids
├── scripts/build-population-grid.py
└── tests/
```
