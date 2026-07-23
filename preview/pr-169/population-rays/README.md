# Population Rays

From any point in the contiguous US: **how far must a thin line go before it
has crossed 1 million people’s homes?**

That’s short in Manhattan (tens of miles) and can be thousands of miles — or
unreachable within the search radius — in places like rural Wyoming. Petal
length on the map is that distance.

## Idea

Walk a bearing from the pin and sum the population of each distinct grid cell
the line first enters. That answers “whose home-cells does this line cross?”
At the packaged resolutions (~0.5–2 km cells), a conceptual 100′ corridor is
thinner than a cell, so centerline cell-crossing is the right discrete model.

Default mode: **distance to 1M people** (petal = miles). Alternate mode: people
along a fixed length (petal ∝ count). Presets for Manhattan / Wyoming, plus
**My location**.

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
