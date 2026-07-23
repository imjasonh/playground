// Browser UI: Leaflet map + directional population rose overlay.

import {
  bearingLabel,
  feetToMeters,
  formatDistance,
  formatPeople,
  metersToMiles,
  milesToMeters,
} from "./geo.js";
import { loadGridFromGzip, pickGrid } from "./grid.js";
import {
  computeRose,
  peopleInCorridor,
  rosePolygon,
  scaledLengths,
} from "./rays.js";

const TIMES_SQUARE = { lat: 40.758, lon: -73.9855 };

const el = {
  status: document.getElementById("status"),
  mode: document.getElementById("mode"),
  widthFt: document.getElementById("width-ft"),
  lengthMi: document.getElementById("length-mi"),
  targetPop: document.getElementById("target-pop"),
  rayCount: document.getElementById("ray-count"),
  lengthControl: document.getElementById("length-control"),
  targetControl: document.getElementById("target-control"),
  originReadout: document.getElementById("origin-readout"),
  hoverReadout: document.getElementById("hover-readout"),
  summary: document.getElementById("summary"),
  dataset: document.getElementById("dataset"),
  reset: document.getElementById("reset-origin"),
};

const state = {
  grids: [],
  origin: { ...TIMES_SQUARE },
  rays: [],
  busy: false,
  hoverBearing: null,
};

let map;
let originMarker;
let roseLayer;
let spokesLayer;
let hoverLine;

function setStatus(text, kind = "") {
  el.status.textContent = text;
  el.status.dataset.kind = kind;
}

function readControls() {
  const mode = el.mode.value;
  const widthM = feetToMeters(Number(el.widthFt.value) || 100);
  const lengthM = milesToMeters(Number(el.lengthMi.value) || 50);
  const targetPeople = Number(el.targetPop.value) || 25_000;
  const rayCount = Number(el.rayCount.value) || 180;
  return {
    mode,
    widthM,
    lengthM,
    targetPeople,
    maxLengthM: milesToMeters(250),
    rayCount,
  };
}

function syncModeControls() {
  const mode = el.mode.value;
  el.lengthControl.hidden = mode !== "fixedLength";
  el.targetControl.hidden = mode !== "fixedPeople";
}

function updateOriginReadout() {
  el.originReadout.textContent = `${state.origin.lat.toFixed(4)}°, ${state.origin.lon.toFixed(4)}°`;
}

function updateSummary() {
  if (!state.rays.length) {
    el.summary.textContent = "Click the map to place an origin.";
    return;
  }
  const opts = readControls();
  if (opts.mode === "fixedLength") {
    let max = state.rays[0];
    let min = state.rays[0];
    let sum = 0;
    for (const r of state.rays) {
      sum += r.people;
      if (r.people > max.people) max = r;
      if (r.people < min.people) min = r;
    }
    el.summary.innerHTML = `
      <div><span>Peak</span><strong>${formatPeople(max.people)}</strong>
      <small>${bearingLabel(max.bearingDeg)} · ${max.bearingDeg.toFixed(0)}°</small></div>
      <div><span>Quietest</span><strong>${formatPeople(min.people)}</strong>
      <small>${bearingLabel(min.bearingDeg)} · ${min.bearingDeg.toFixed(0)}°</small></div>
      <div><span>Mean / ray</span><strong>${formatPeople(sum / state.rays.length)}</strong>
      <small>within ${metersToMiles(opts.lengthM).toFixed(0)} mi</small></div>`;
  } else {
    const finite = state.rays.filter((r) => Number.isFinite(r.lengthM));
    if (!finite.length) {
      el.summary.textContent = `No direction reaches ${formatPeople(opts.targetPeople)} within ${metersToMiles(opts.maxLengthM).toFixed(0)} mi.`;
      return;
    }
    let nearest = finite[0];
    let farthest = finite[0];
    for (const r of finite) {
      if (r.lengthM < nearest.lengthM) nearest = r;
      if (r.lengthM > farthest.lengthM) farthest = r;
    }
    el.summary.innerHTML = `
      <div><span>Nearest ${formatPeople(opts.targetPeople)}</span><strong>${formatDistance(nearest.lengthM)}</strong>
      <small>${bearingLabel(nearest.bearingDeg)} · ${nearest.bearingDeg.toFixed(0)}°</small></div>
      <div><span>Farthest (reached)</span><strong>${formatDistance(farthest.lengthM)}</strong>
      <small>${bearingLabel(farthest.bearingDeg)} · ${farthest.bearingDeg.toFixed(0)}°</small></div>
      <div><span>Directions reached</span><strong>${finite.length}/${state.rays.length}</strong>
      <small>within ${metersToMiles(opts.maxLengthM).toFixed(0)} mi</small></div>`;
  }
}

function updateHoverReadout() {
  if (state.hoverBearing == null || !state.rays.length) {
    el.hoverReadout.textContent = "Hover a petal for a bearing.";
    return;
  }
  const opts = readControls();
  const step = 360 / state.rays.length;
  let best = state.rays[0];
  let bestDiff = 180;
  for (const r of state.rays) {
    let d = Math.abs(r.bearingDeg - state.hoverBearing);
    if (d > 180) d = 360 - d;
    if (d < bestDiff) {
      bestDiff = d;
      best = r;
    }
  }
  if (bestDiff > step) {
    el.hoverReadout.textContent = "Hover a petal for a bearing.";
    return;
  }
  if (opts.mode === "fixedLength") {
    el.hoverReadout.textContent = `${bearingLabel(best.bearingDeg)} ${best.bearingDeg.toFixed(0)}° — ${formatPeople(best.people)} within ${metersToMiles(opts.lengthM).toFixed(0)} mi`;
  } else if (Number.isFinite(best.lengthM)) {
    el.hoverReadout.textContent = `${bearingLabel(best.bearingDeg)} ${best.bearingDeg.toFixed(0)}° — ${formatPeople(opts.targetPeople)} in ${formatDistance(best.lengthM)}`;
  } else {
    el.hoverReadout.textContent = `${bearingLabel(best.bearingDeg)} ${best.bearingDeg.toFixed(0)}° — ${formatPeople(opts.targetPeople)} not reached`;
  }
}

function rayLengths(opts) {
  if (opts.mode === "fixedPeople") {
    return state.rays.map((r) => (Number.isFinite(r.lengthM) ? r.lengthM : 0));
  }
  return scaledLengths(state.rays, opts.lengthM);
}

function tipLatLng(bearingDeg, lengthM) {
  const ring = rosePolygon(
    state.origin,
    [{ bearingDeg }],
    () => lengthM,
  );
  return ring[0];
}

function drawRose() {
  if (roseLayer) {
    map.removeLayer(roseLayer);
    roseLayer = null;
  }
  if (spokesLayer) {
    map.removeLayer(spokesLayer);
    spokesLayer = null;
  }
  if (!state.rays.length) return;

  const opts = readControls();
  const lengths = rayLengths(opts);
  const lengthByBearing = new Map(
    state.rays.map((r, i) => [r.bearingDeg, lengths[i] || 0]),
  );
  const poly = rosePolygon(
    state.origin,
    state.rays,
    (ray) => lengthByBearing.get(ray.bearingDeg) || 0,
  );

  roseLayer = L.polygon(poly, {
    color: "#d97706",
    weight: 1.5,
    opacity: 0.95,
    fillColor: "#f59e0b",
    fillOpacity: 0.28,
    interactive: true,
  }).addTo(map);

  const spokes = [];
  for (const bearing of [0, 90, 180, 270]) {
    const len =
      lengthByBearing.get(bearing) ??
      lengths[
        state.rays.findIndex(
          (r) => Math.abs(r.bearingDeg - bearing) < 360 / state.rays.length / 2,
        )
      ] ??
      0;
    if (!(len > 0)) continue;
    spokes.push([
      [state.origin.lat, state.origin.lon],
      tipLatLng(bearing, len),
    ]);
  }
  spokesLayer = L.polyline(spokes, {
    color: "#92400e",
    weight: 1,
    opacity: 0.55,
    dashArray: "4 6",
    interactive: false,
  }).addTo(map);
}

async function recompute() {
  if (state.busy || !state.grids.length) return;
  const grid = pickGrid(state.grids, state.origin.lat, state.origin.lon);
  if (!grid) {
    setStatus("Origin is outside the loaded US grid.", "warn");
    state.rays = [];
    drawRose();
    updateSummary();
    return;
  }
  el.dataset.textContent = `${grid.meta.key || "grid"} · ${grid.meta.note || ""}`;
  state.busy = true;
  setStatus("Computing corridors…");
  const opts = readControls();
  // Yield so the status can paint.
  await new Promise((r) => setTimeout(r, 0));
  try {
    state.rays = computeRose(grid, state.origin, opts);
    drawRose();
    updateSummary();
    updateHoverReadout();
    setStatus("Ready — drag the pin or click the map.", "ok");
  } catch (err) {
    console.error(err);
    setStatus(String(err.message || err), "warn");
  } finally {
    state.busy = false;
  }
}

function setOrigin(lat, lon, pan = false) {
  state.origin = { lat, lon };
  originMarker.setLatLng([lat, lon]);
  updateOriginReadout();
  if (pan) map.panTo([lat, lon]);
  recompute();
}

function initMap() {
  map = L.map("map", {
    zoomControl: true,
    scrollWheelZoom: true,
  }).setView([TIMES_SQUARE.lat, TIMES_SQUARE.lon], 9);

  L.tileLayer("https://{s}.basemaps.cartocdn.com/light_all/{z}/{x}/{y}{r}.png", {
    attribution:
      '&copy; <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a> &copy; <a href="https://carto.com/attributions">CARTO</a>',
    subdomains: "abcd",
    maxZoom: 18,
  }).addTo(map);

  originMarker = L.marker([TIMES_SQUARE.lat, TIMES_SQUARE.lon], {
    draggable: true,
    title: "Origin",
  }).addTo(map);

  originMarker.on("dragend", () => {
    const ll = originMarker.getLatLng();
    setOrigin(ll.lat, ll.lng);
  });

  map.on("click", (e) => {
    setOrigin(e.latlng.lat, e.latlng.lng);
  });

  map.on("mousemove", (e) => {
    if (!state.rays.length) return;
    const dLat = e.latlng.lat - state.origin.lat;
    const dLon = e.latlng.lng - state.origin.lon;
    // rough local bearing
    const { lat: mLat, lon: mLon } = (() => {
      const φ = (state.origin.lat * Math.PI) / 180;
      return {
        lat: 111132.92 - 559.82 * Math.cos(2 * φ),
        lon: Math.max(111412.84 * Math.cos(φ), 1),
      };
    })();
    const x = dLon * mLon;
    const y = dLat * mLat;
    const bearing = ((Math.atan2(x, y) * 180) / Math.PI + 360) % 360;
    state.hoverBearing = bearing;
    updateHoverReadout();

    const opts = readControls();
    const step = 360 / state.rays.length;
    let best = state.rays[0];
    let bestDiff = 180;
    for (const r of state.rays) {
      let d = Math.abs(r.bearingDeg - bearing);
      if (d > 180) d = 360 - d;
      if (d < bestDiff) {
        bestDiff = d;
        best = r;
      }
    }
    const lengths = rayLengths(opts);
    const len = lengths[state.rays.indexOf(best)] || 0;
    if (hoverLine) map.removeLayer(hoverLine);
    if (len > 0 && bestDiff <= step * 1.5) {
      hoverLine = L.polyline(
        [
          [state.origin.lat, state.origin.lon],
          tipLatLng(best.bearingDeg, len),
        ],
        { color: "#0f766e", weight: 3, opacity: 0.9 },
      ).addTo(map);
    }
  });
}

async function fetchJson(path) {
  const res = await fetch(path);
  if (!res.ok) throw new Error(`HTTP ${res.status} for ${path}`);
  return res.json();
}

async function loadDatasets() {
  setStatus("Loading population grids…");
  const index = await fetchJson("data/index.json");
  const grids = [];
  for (const key of index.datasets) {
    const meta = await fetchJson(`data/${key}.json`);
    const res = await fetch(`data/${meta.file}`);
    if (!res.ok) throw new Error(`HTTP ${res.status} for ${meta.file}`);
    const buf = new Uint8Array(await res.arrayBuffer());
    const grid = await loadGridFromGzip(meta, buf);
    grids.push(grid);
    setStatus(`Loaded ${key}…`);
  }
  state.grids = grids;
  el.dataset.textContent = `${grids.length} grids ready`;
}

function bindControls() {
  for (const node of [
    el.mode,
    el.widthFt,
    el.lengthMi,
    el.targetPop,
    el.rayCount,
  ]) {
    node.addEventListener("change", () => {
      syncModeControls();
      recompute();
    });
  }
  el.reset.addEventListener("click", () => {
    setOrigin(TIMES_SQUARE.lat, TIMES_SQUARE.lon, true);
    map.setZoom(9);
  });
  syncModeControls();
  updateOriginReadout();
}

async function main() {
  initMap();
  bindControls();
  try {
    await loadDatasets();
    await recompute();
    // Sanity probe for the Manhattan story in the console.
    const grid = pickGrid(state.grids, TIMES_SQUARE.lat, TIMES_SQUARE.lon);
    if (grid) {
      const w = feetToMeters(100);
      const Lmi = milesToMeters(30);
      const west = peopleInCorridor(grid, TIMES_SQUARE, 270, Lmi, w);
      const se = peopleInCorridor(grid, TIMES_SQUARE, 135, Lmi, w);
      console.info(
        `Probe 100′ × 30 mi from Times Square — W: ${formatPeople(west)}, SE: ${formatPeople(se)}`,
      );
    }
  } catch (err) {
    console.error(err);
    setStatus(`Failed to load data: ${err.message || err}`, "warn");
  }
}

main();
