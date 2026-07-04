# nypd-choppers

A browser app that reconstructs **daily flight paths, airborne hours, and
estimated fuel cost** for the **NYPD Aviation Unit** helicopter fleet from
public **ADS-B** data.

It answers three questions per day:

- **How many hours** were NYPD helicopters airborne?
- **Where** did they fly? (approximate ground tracks on a map)
- **How much fuel** did they likely burn, and **what did it cost**?

This is not a real-time tracker. It is a daily-estimate tool built from coarse,
~hourly position samples.

## Why this app has an unusual lifecycle

Free ADS-B aggregators can't be queried directly from the browser (no CORS) and
only expose **live** positions, not history. So unlike the other apps in this
repo, `nypd-choppers` ships with a **scheduled data-collection workflow**:

- [`.github/workflows/nypd-choppers-scrape.yml`](../.github/workflows/nypd-choppers-scrape.yml)
  runs **hourly**, looks up each fleet aircraft's current position via
  [adsb.lol](https://adsb.lol) (with adsb.fi / airplanes.live fallbacks), and
  appends airborne snapshots to per-day JSON files.
- Those files are committed **directly to the `gh-pages` branch** under
  `nypd-choppers/data/` — never to `main`. The deployed app fetches them at
  runtime. This keeps the app's source clean and means no API is ever called
  from the browser.
- The workflow shares the `gh-pages-publish` concurrency group with the deploy,
  preview, and cleanup workflows, so the published branch is only ever touched
  by one job at a time.

This lifecycle is intentionally **specific to this app** and is not generalized
to the rest of the playground.

```
Browser (static)  ──fetch──▶  gh-pages: nypd-choppers/data/*.json
                                        ▲
                                        │ hourly commit
                          GitHub Actions scraper ──▶ adsb.lol / adsb.fi / airplanes.live
```

## The fleet

Aircraft are identified by FAA tail number, converted to the ICAO Mode-S hex
they broadcast (see `src/nnumber.js`; the derivation is checked against publicly
reported hex codes in the tests):

| Tail | Model | Est. burn (gal/hr) |
|------|-------|--------------------|
| N917PD–N920PD | Bell 429 | ~50 |
| N922PD | Subaru Bell 412EPX | ~100 |
| N412PD, N414PD, N422PD | Bell 412EP | ~100 |
| N407NY | Bell 407 | ~40 |

## Estimation method (and its limits)

- The scraper samples each aircraft roughly **once per hour** and keeps only
  airborne snapshots. Map paths connect those hourly points, so they are
  **coarse approximations**, not continuous tracks.
- **Airborne time** for a flight = observed span (first→last sample) **plus one
  sampling interval**, so an aircraft seen by a single scrape counts as ~1 hour
  aloft. This avoids under-counting brief flights but is only an estimate.
- **Fuel** = estimated airborne hours × per-model cruise burn.
  **Cost** = fuel × the Jet-A price (editable in the UI, default $6.50/gal).
- All figures are **order-of-magnitude estimates** for public interest, not
  operational, safety, or budget data.

## Data format

`data/index.json`:

```json
{ "generator": "nypd-choppers scraper", "updated": 1710000000,
  "days": [ { "date": "2026-07-04", "samples": 12 } ] }
```

`data/YYYY-MM-DD.json`:

```json
{ "date": "2026-07-04", "tz": "America/New_York", "updated": 1710000000,
  "samples": [
    { "hex": "ACB1F5", "r": "N917PD", "t": 1710000000,
      "lat": 40.7, "lon": -74.0, "alt": 1200, "gs": 90, "track": 180,
      "ground": false }
  ] }
```

Until the live scraper has published anything, the app falls back to the bundled
demo data in [`sample/`](sample/) and shows a "sample data" badge.

## Develop & test

```bash
cd nypd-choppers
npm install
npm test          # node --test: N-number, fleet, analysis, scrape helpers
npm start         # static server on http://localhost:3000 (shows sample data)

# Run the scraper locally (writes to ./data, which is gitignored):
npm run scrape
```

## Layout

```
nypd-choppers/
├── index.html            # UI shell (Leaflet map, summary, table)
├── styles.css
├── favicon.svg
├── src/
│   ├── app.js            # browser wiring (DOM + Leaflet)
│   ├── nnumber.js        # FAA N-number → ICAO hex converter
│   ├── fleet.js          # NYPD fleet roster + fuel burn + colours
│   ├── analysis.js       # flights, airborne time, distance, fuel, cost (pure)
│   └── scrape-lib.js     # ADS-B response → samples, day-file merge (pure)
├── scripts/scrape.js     # hourly scraper entry point (network + file IO)
├── tests/                # node --test unit tests
└── sample/               # bundled demo data used before first live scrape
```
