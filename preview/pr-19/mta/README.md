# NYC Subway Live

A client-side browser app that shows **realtime NYC subway arrivals, train
locations, and service status** straight from the MTA's public
[GTFS-realtime feeds](https://api.mta.info/) — no build step, no server, no API
key.

Pick a station and you get:

- **Arrival board** — upcoming trains by direction with live countdowns and the
  destination terminal, soonest first.
- **Trains in service** — where each train is right now ("Stopped at …",
  "Approaching …", "En route to …"), flagging the ones at your station.
- **Service status** — a Good Service / Delays / Planned Work / Service Change
  pill for every line, plus the underlying alerts (tap a line to filter).

## Running locally

```bash
cd mta
npm install          # only needed for the test tooling
npm start            # serves the static app at http://localhost:3000
```

The app itself is plain ES modules + HTML/CSS — you can also just open
`index.html` through any static file server.

## Data sources & the CORS catch

| What | Feed |
|------|------|
| Trip updates + vehicle positions | `…/nyct%2Fgtfs`, `…/nyct%2Fgtfs-ace`, `-bdfm`, `-g`, `-jz`, `-nqrw`, `-l`, `-si` |
| Service alerts | `…/camsys%2Fall-alerts` |

Base URL: `https://api-endpoint.mta.info/Dataservice/mtagtfsfeeds/`.

These feeds need **no API key**, but they are **protobuf-encoded** and are served
**without CORS headers**, so a browser on another origin (like GitHub Pages)
**cannot fetch them directly**. The app handles this two ways:

- **Sample data (default).** Realistic feeds are generated in-browser and run
  through the exact same decode pipeline as live data, so the app is fully
  functional offline and on first load. Great for demos and tests.
- **Live MTA feeds.** Switch the data source in *Settings* and pick a **CORS
  proxy** (or point it at your own). MTA requests are routed through the proxy,
  decoded client-side, and rendered. Public proxies are best-effort and may
  rate-limit; a self-hosted proxy is the reliable option.

Proxy templates use `{url}` (URL-encoded feed URL) or `{rawurl}` (raw); an empty
template requests the MTA directly.

## How it works

GTFS-realtime is plain Protocol Buffers, so the app ships a tiny hand-rolled
protobuf reader/writer (`src/protobuf.js`) — no heavyweight dependency — and a
field-by-field decoder (`src/gtfsRealtime.js`). Everything downstream is pure,
`now`-injectable functions that are easy to test:

```
feeds.js        which feed serves which line + upstream URLs
proxy.js        feed URL + proxy template -> the URL actually fetched
client.js       fetch one feed and decode it (transport injectable)
stations.js     station registry, transfer-complex grouping, stop-id parsing
arrivals.js     decoded line feed + a complex -> arrival board (by direction)
trains.js       decoded line feed -> "where the trains are" list
status.js       decoded alerts feed -> per-line status + alert list
sampleFeed.js   build realistic feeds (encoded to real protobuf bytes)
app.js          DOM wiring, settings, and the refresh poller
```

## Tests

```bash
npm test         # Jest unit tests (protobuf round-trips, decoders, transforms)
npm run test:e2e # Playwright desktop + mobile smoke tests (offline/sample mode)
```

The e2e specs run entirely against sample data, so they need no network. One
desktop spec also intercepts a request with a fixture protobuf to exercise the
live fetch + decode path deterministically.

## Updating station data

`src/stationsData.js` is generated from the MIT-licensed
[`mta-subway-stations`](https://www.npmjs.com/package/mta-subway-stations)
package (a mirror of the MTA Open Data "Stations" table). To refresh it:

```bash
npm pack mta-subway-stations && tar xzf mta-subway-stations-*.tgz
# transform package/stations.json -> src/stationsData.js
# keep fields: GTFS Stop ID, Stop Name, Complex ID, Daytime Routes,
#              Borough, lat/lon, North/South Direction Label
```

Not affiliated with the MTA. Subway line names, bullets, and colors are
trademarks of the Metropolitan Transportation Authority.
