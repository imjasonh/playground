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
their live endpoints only expose an aircraft's **current** position — far too
sparse to reconstruct flight paths or airborne time. So unlike the other apps in
this repo, `nypd-choppers` ships with a **scheduled data-collection workflow**:

- [`.github/workflows/nypd-choppers-scrape.yml`](../.github/workflows/nypd-choppers-scrape.yml)
  runs **hourly** and fetches each fleet aircraft's full-day **trace** from
  [adsb.lol](https://adsb.lol) — the same dense (~30&nbsp;s) position history the
  tracking networks use to draw a flight path
  (`.../data/traces/<xx>/trace_full_<hex>.json`, readsb/tar1090 format).
- Each run re-fetches the whole current day and **merges** it (de-duplicated) by
  New York calendar date, so brief flights that start and end between runs are
  never missed. If no trace host is reachable, it falls back to the live
  `/v2/hex` snapshot so a run still records something.
- The merged files are committed **directly to the `gh-pages` branch** under
  `nypd-choppers/data/` — never to `main`. The deployed app fetches them at
  runtime, so no API is ever called from the browser.
- The workflow shares the `gh-pages-publish` concurrency group with the deploy,
  preview, and cleanup workflows, so the published branch is only ever touched
  by one job at a time.

This lifecycle is intentionally **specific to this app** and is not generalized
to the rest of the playground.

```
Browser (static)  ──fetch──▶  gh-pages: nypd-choppers/data/*.json
                                        ▲
                                        │ hourly merge + commit
              GitHub Actions collector ──▶ adsb.lol full-day traces
                                           (snapshot fallback: adsb.lol/adsb.fi/airplanes.live)
```

> **Why traces, not hourly snapshots?** Sampling the live position once per hour
> yields one point per hour and misses any flight shorter than the gap between
> runs. A full-day trace is the aircraft's complete, dense track for the day, so
> even fetched "late" it gives accurate paths and airborne time.

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

- Paths are drawn from the dense trace points, so they follow the actual route.
  Flights are split on long gaps and on the trace's takeoff/landing (new-leg)
  markers.
- Each path segment can be **shaded by barometric altitude** (the *Path color*
  control, default). The ramp runs cool→warm (blue = low, red = high) and is
  normalised to the altitude range of the tracks currently shown, so climbs and
  descents stand out even for low-flying helicopters; switch to *Aircraft* to
  colour whole paths by tail instead.
- **Airborne time** for a flight = observed span (first→last airborne sample)
  plus one observation interval. The interval is **derived from the data**
  (tens of seconds for dense trace data → airborne time is close to actual; up
  to an hour for sparse fallback data → each detection counts ~1 hour).
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
      "ground": false, "leg": false }
  ] }
```

(`alt` is `null` when unknown; `ground: true` marks on-ground samples; `leg:
true` marks a takeoff/landing boundary from the trace.)

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
│   ├── altitude.js       # altitude → colour ramp for map traces (pure)
│   ├── analysis.js       # flights, airborne time, distance, fuel, cost (pure)
│   ├── trace.js          # readsb/tar1090 trace → samples (pure)
│   └── scrape-lib.js     # ADS-B response → samples, day-file merge (pure)
├── scripts/scrape.js     # hourly collector entry point (network + file IO)
├── tests/                # node --test unit tests
└── sample/               # bundled demo data used before first live scrape
```
