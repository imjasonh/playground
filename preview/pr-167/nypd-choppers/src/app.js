// Browser entry point: loads scraped ADS-B data, runs the analysis, and paints
// the map, summary cards, and per-aircraft table. All heavy lifting lives in
// the DOM-free analysis.js / fleet.js modules (which are unit-tested).

import { FLEET, FLEET_BY_HEX } from "./fleet.js";
import {
  aggregateDays,
  analyzeDay,
  formatDuration,
  kmToMiles,
} from "./analysis.js";

const NYC = [40.7128, -74.006];
const ALL_DAYS = "__all__";

const state = {
  base: "data", // "data" (live) or "sample" (fallback demo)
  index: null, // { days: [{date, samples}] }
  dayCache: new Map(), // date -> { samples: [...] }
  selectedDay: null,
};

const el = {
  daySelect: document.getElementById("day-select"),
  price: document.getElementById("price"),
  refresh: document.getElementById("refresh"),
  summary: document.getElementById("summary"),
  rows: document.getElementById("aircraft-rows"),
  emptyNote: document.getElementById("empty-note"),
  legend: document.getElementById("legend"),
  badge: document.getElementById("source-badge"),
};

let map;
let flightLayer;

function initMap() {
  map = L.map("map", { scrollWheelZoom: true }).setView(NYC, 10);
  L.tileLayer("https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png", {
    attribution: "&copy; OpenStreetMap contributors",
    maxZoom: 18,
  }).addTo(map);
  flightLayer = L.layerGroup().addTo(map);
}

async function fetchJson(path) {
  const res = await fetch(path, { cache: "no-store" });
  if (!res.ok) throw new Error(`HTTP ${res.status} for ${path}`);
  return res.json();
}

// Resolve the data source: prefer live scraped data, fall back to bundled
// sample data so the app is never empty during local dev or before first scrape.
async function loadIndex() {
  try {
    const idx = await fetchJson("data/index.json");
    if (idx && Array.isArray(idx.days) && idx.days.length > 0) {
      state.base = "data";
      state.index = idx;
      setBadge("live", "Live scraped data");
      return;
    }
  } catch {
    /* fall through to sample */
  }
  const sample = await fetchJson("sample/index.json");
  state.base = "sample";
  state.index = sample;
  setBadge("demo", "Sample data \u2014 live scrape not published yet");
}

function setBadge(kind, text) {
  el.badge.textContent = text;
  el.badge.className = `badge ${kind}`;
  el.badge.hidden = false;
}

async function loadDay(date) {
  if (state.dayCache.has(date)) return state.dayCache.get(date);
  const day = await fetchJson(`${state.base}/${date}.json`);
  const samples = Array.isArray(day.samples) ? day.samples : [];
  state.dayCache.set(date, { samples, meta: day });
  return state.dayCache.get(date);
}

function populateDays() {
  const days = state.index.days.slice().sort((a, b) => b.date.localeCompare(a.date));
  el.daySelect.innerHTML = "";
  const all = document.createElement("option");
  all.value = ALL_DAYS;
  all.textContent = `All ${days.length} day${days.length === 1 ? "" : "s"}`;
  el.daySelect.appendChild(all);
  for (const d of days) {
    const opt = document.createElement("option");
    opt.value = d.date;
    opt.textContent = formatDayLabel(d.date);
    el.daySelect.appendChild(opt);
  }
  // Default to the most recent single day.
  state.selectedDay = days.length ? days[0].date : ALL_DAYS;
  el.daySelect.value = state.selectedDay;
}

function formatDayLabel(date) {
  const d = new Date(`${date}T12:00:00`);
  return d.toLocaleDateString(undefined, {
    weekday: "short",
    year: "numeric",
    month: "short",
    day: "numeric",
  });
}

function currentPrice() {
  const v = parseFloat(el.price.value);
  return Number.isFinite(v) && v >= 0 ? v : 0;
}

async function render() {
  const price = currentPrice();
  const ctx = { fleet: FLEET, fleetByHex: FLEET_BY_HEX };
  const selection = el.daySelect.value;

  let analysis;
  let allSamples = [];
  if (selection === ALL_DAYS) {
    const results = [];
    for (const d of state.index.days) {
      const { samples } = await loadDay(d.date);
      allSamples = allSamples.concat(samples);
      results.push(analyzeDay(samples, ctx, { pricePerGallon: price }));
    }
    analysis = aggregateDays(results);
    analysis.totals.days = state.index.days.length;
  } else {
    const { samples } = await loadDay(selection);
    allSamples = samples;
    analysis = analyzeDay(samples, ctx, { pricePerGallon: price });
    // Keep a per-flight view for the map on single days.
    analysis.perDaySingle = true;
  }

  renderSummary(analysis, selection);
  renderTable(analysis);
  renderMap(selection, allSamples, price, ctx);
}

function renderSummary(analysis, selection) {
  const t = analysis.totals;
  const cards = [
    {
      value: formatDuration(t.estimatedSeconds),
      label: "Estimated airborne",
      sub: selection === ALL_DAYS ? `across ${t.days} days` : "this day",
    },
    { value: String(t.flightCount), label: "Flights", sub: `${t.activeAircraft ?? analysis.perAircraft.length} aircraft aloft` },
    { value: `${Math.round(kmToMiles(t.distanceKm)).toLocaleString()} mi`, label: "Distance flown", sub: `${Math.round(t.distanceKm).toLocaleString()} km` },
    { value: `${Math.round(t.estimatedGallons).toLocaleString()} gal`, label: "Estimated Jet-A", sub: "turbine cruise burn" },
    { value: fmtMoney(t.estimatedCost), label: "Estimated fuel cost", sub: `@ ${fmtMoney(currentPrice())}/gal` },
  ];
  el.summary.innerHTML = cards
    .map(
      (c) => `<div class="card"><div class="value">${c.value}</div>` +
        `<div class="label">${c.label}</div><div class="sub">${c.sub}</div></div>`,
    )
    .join("");
}

function renderTable(analysis) {
  const rows = analysis.perAircraft;
  if (!rows.length) {
    el.rows.innerHTML = "";
    el.emptyNote.hidden = false;
    el.emptyNote.textContent =
      "No NYPD helicopters were tracked airborne in this period.";
    return;
  }
  el.emptyNote.hidden = true;
  el.rows.innerHTML = rows
    .map((a) => {
      const miles = Math.round(kmToMiles(a.distanceKm)).toLocaleString();
      return (
        `<tr>` +
        `<td><span class="tail-cell"><span class="swatch" style="background:${a.color}"></span>${a.tail ?? a.hex}</span></td>` +
        `<td>${a.model ?? "&mdash;"}</td>` +
        `<td class="num">${a.flightCount}</td>` +
        `<td class="num">${formatDuration(a.estimatedSeconds)}</td>` +
        `<td class="num">${miles} mi</td>` +
        `<td class="num">${Math.round(a.estimatedGallons).toLocaleString()} gal</td>` +
        `<td class="num">${fmtMoney(a.estimatedCost)}</td>` +
        `</tr>`
      );
    })
    .join("");
}

// Draw flight paths for the given samples. For a single day this shows the
// detailed per-flight segments; for "all days" it overlays everything.
function renderMap(selection, samples, price, ctx) {
  flightLayer.clearLayers();
  const perAircraft = analyzeDay(samples, ctx, { pricePerGallon: price }).perAircraft;
  const bounds = [];
  const legendItems = [];

  for (const a of perAircraft) {
    let drewAny = false;
    for (const flight of a.flights) {
      const latlngs = flight.points.map((p) => [p.lat, p.lon]);
      latlngs.forEach((ll) => bounds.push(ll));
      if (latlngs.length >= 2) {
        L.polyline(latlngs, { color: a.color, weight: 3, opacity: 0.85 }).addTo(flightLayer);
        drewAny = true;
      }
      // Start marker for each flight.
      const start = flight.points[0];
      L.circleMarker([start.lat, start.lon], {
        radius: 4,
        color: a.color,
        fillColor: a.color,
        fillOpacity: 0.9,
        weight: 1,
      })
        .bindPopup(
          `<strong>${a.tail ?? a.hex}</strong><br>${a.model ?? ""}<br>` +
            `Flight ${formatDuration(flight.estimatedSeconds)} \u00b7 ` +
            `${Math.round(kmToMiles(flight.distanceKm))} mi (est.)`,
        )
        .addTo(flightLayer);
      drewAny = true;
    }
    if (drewAny) legendItems.push(a);
  }

  renderLegend(legendItems);

  if (bounds.length) {
    map.fitBounds(bounds, { padding: [30, 30], maxZoom: 12 });
  } else {
    map.setView(NYC, 10);
  }
}

function renderLegend(items) {
  if (!items.length) {
    el.legend.classList.remove("show");
    el.legend.innerHTML = "";
    return;
  }
  el.legend.innerHTML = items
    .map(
      (a) =>
        `<div class="legend-item"><span class="swatch" style="background:${a.color}"></span>` +
        `${a.tail ?? a.hex}</div>`,
    )
    .join("");
  el.legend.classList.add("show");
}

function fmtMoney(n) {
  return n.toLocaleString(undefined, {
    style: "currency",
    currency: "USD",
    maximumFractionDigits: 0,
  });
}

async function boot() {
  initMap();
  try {
    await loadIndex();
    populateDays();
    await render();
  } catch (err) {
    el.emptyNote.hidden = false;
    el.emptyNote.textContent = `Could not load flight data: ${err.message}`;
    setBadge("demo", "No data available");
  }
}

el.daySelect.addEventListener("change", () => {
  render().catch((e) => console.error(e));
});
el.price.addEventListener("change", () => {
  render().catch((e) => console.error(e));
});
el.refresh.addEventListener("click", async () => {
  state.dayCache.clear();
  try {
    await loadIndex();
    populateDays();
    await render();
  } catch (e) {
    console.error(e);
  }
});

boot();
