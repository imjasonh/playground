// Browser UI: Leaflet map + directional population rose overlay.

import {
  bearingLabel,
  feetToMeters,
  formatDistance,
  formatPeople,
  metersToMiles,
  milesToMeters,
} from "./geo.js";
import { loadGridFromGzip, pickGrid, pickGridForTarget } from "./grid.js";
import {
  computeRose,
  distanceToPeople,
  rosePolygon,
  scaledLengths,
} from "./rays.js";

const PLACES = {
  manhattan: {
    lat: 40.758,
    lon: -73.9855,
    zoom: 9,
    label: "Times Square, Manhattan",
  },
  wyoming: {
    lat: 43.076,
    lon: -107.2903,
    zoom: 6,
    label: "Central Wyoming",
  },
};

/** Fixed 5° segments around the compass. */
const RAY_COUNT = 72;

const el = {
  status: document.getElementById("status"),
  mode: document.getElementById("mode"),
  widthFt: document.getElementById("width-ft"),
  lengthMi: document.getElementById("length-mi"),
  lengthReadout: document.getElementById("length-mi-readout"),
  targetPop: document.getElementById("target-pop"),
  targetReadout: document.getElementById("target-pop-readout"),
  lengthControl: document.getElementById("length-control"),
  targetControl: document.getElementById("target-control"),
  originReadout: document.getElementById("origin-readout"),
  hoverReadout: document.getElementById("hover-readout"),
  summary: document.getElementById("summary"),
  dataset: document.getElementById("dataset"),
  myLocation: document.getElementById("my-location"),
  heroLabel: document.getElementById("hero-label"),
  heroValue: document.getElementById("hero-value"),
  heroDetail: document.getElementById("hero-detail"),
  mapHint: document.getElementById("map-hint"),
};

const state = {
  grids: [],
  origin: { ...PLACES.manhattan },
  rays: [],
  busy: false,
  hoverBearing: null,
  placeLabel: PLACES.manhattan.label,
};

let map;
let originMarker;
let roseLayer;
let openLayer;
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
  const targetPeople = Number(el.targetPop.value) || 1_000_000;
  // Long enough that rural West can show multi-thousand-mile answers.
  const maxLengthM = milesToMeters(mode === "fixedPeople" ? 3000 : 250);
  return {
    mode,
    widthM,
    lengthM,
    targetPeople,
    maxLengthM,
    rayCount: RAY_COUNT,
  };
}

function syncSliderReadouts() {
  el.lengthReadout.textContent = `${Number(el.lengthMi.value)} mi`;
  el.targetReadout.textContent = formatPeople(Number(el.targetPop.value));
}

function syncModeControls() {
  const mode = el.mode.value;
  el.lengthControl.hidden = mode !== "fixedLength";
  el.targetControl.hidden = mode !== "fixedPeople";
  syncSliderReadouts();
  if (mode === "fixedPeople") {
    el.mapHint.textContent =
      "Petal length = miles to reach the target · dashed = not reached yet · click to move";
  } else {
    el.mapHint.textContent =
      "Petal length ∝ people along a fixed line · click to move the pin";
  }
}

function updateOriginReadout() {
  const place = state.placeLabel ? `${state.placeLabel} · ` : "";
  el.originReadout.textContent = `${place}${state.origin.lat.toFixed(4)}°, ${state.origin.lon.toFixed(4)}°`;
}

function updateHero() {
  const opts = readControls();
  if (!state.rays.length) {
    el.heroLabel.textContent = `Shortest line to ${formatPeople(opts.targetPeople)}`;
    el.heroValue.textContent = "—";
    el.heroDetail.textContent = "Place a pin to measure.";
    return;
  }
  if (opts.mode === "fixedPeople") {
    const reached = state.rays.filter((r) => r.reached);
    el.heroLabel.textContent = `Shortest line to ${formatPeople(opts.targetPeople)}`;
    if (!reached.length) {
      el.heroValue.textContent = `>${metersToMiles(opts.maxLengthM).toFixed(0)} mi`;
      el.heroDetail.textContent = `No direction hits ${formatPeople(opts.targetPeople)} within ${metersToMiles(opts.maxLengthM).toFixed(0)} miles — try a denser place.`;
      return;
    }
    let nearest = reached[0];
    for (const r of reached) if (r.lengthM < nearest.lengthM) nearest = r;
    el.heroValue.textContent = formatDistance(nearest.lengthM);
    el.heroDetail.textContent = `${bearingLabel(nearest.bearingDeg)} · ${nearest.bearingDeg.toFixed(0)}° — compare Manhattan (short) vs Wyoming (long).`;
  } else {
    let peak = state.rays[0];
    for (const r of state.rays) if (r.people > peak.people) peak = r;
    el.heroLabel.textContent = `Most people along ${metersToMiles(opts.lengthM).toFixed(0)} mi`;
    el.heroValue.textContent = formatPeople(peak.people);
    el.heroDetail.textContent = `${bearingLabel(peak.bearingDeg)} · ${peak.bearingDeg.toFixed(0)}°`;
  }
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
    for (const r of state.rays) {
      if (r.people > max.people) max = r;
      if (r.people < min.people) min = r;
    }
    el.summary.innerHTML = `
      <div><span>Peak direction</span><strong>${formatPeople(max.people)}</strong>
      <small>${bearingLabel(max.bearingDeg)} · ${max.bearingDeg.toFixed(0)}°</small></div>
      <div><span>Quietest</span><strong>${formatPeople(min.people)}</strong>
      <small>${bearingLabel(min.bearingDeg)} · ${min.bearingDeg.toFixed(0)}°</small></div>`;
  } else {
    const reached = state.rays.filter((r) => r.reached);
    const missed = state.rays.length - reached.length;
    if (!reached.length) {
      el.summary.innerHTML = `
        <div><span>Story</span><strong>Sparse country</strong>
        <small>Every direction needs more than ${metersToMiles(opts.maxLengthM).toFixed(0)} mi to gather ${formatPeople(opts.targetPeople)}.</small></div>`;
      return;
    }
    let nearest = reached[0];
    let farthest = reached[0];
    for (const r of reached) {
      if (r.lengthM < nearest.lengthM) nearest = r;
      if (r.lengthM > farthest.lengthM) farthest = r;
    }
    el.summary.innerHTML = `
      <div><span>Nearest</span><strong>${formatDistance(nearest.lengthM)}</strong>
      <small>${bearingLabel(nearest.bearingDeg)}</small></div>
      <div><span>Farthest (reached)</span><strong>${formatDistance(farthest.lengthM)}</strong>
      <small>${bearingLabel(farthest.bearingDeg)}</small></div>
      <div><span>Not reached</span><strong>${missed}/${state.rays.length}</strong>
      <small>dashed petals stop at ${metersToMiles(opts.maxLengthM).toFixed(0)} mi</small></div>`;
  }
}

function updateHoverReadout() {
  if (state.hoverBearing == null || !state.rays.length) {
    el.hoverReadout.textContent = "Hover the map around the pin.";
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
    el.hoverReadout.textContent = "Hover the map around the pin.";
    return;
  }
  if (opts.mode === "fixedLength") {
    el.hoverReadout.textContent = `${bearingLabel(best.bearingDeg)} ${best.bearingDeg.toFixed(0)}° — ${formatPeople(best.people)} along ${metersToMiles(opts.lengthM).toFixed(0)} mi`;
  } else if (best.reached) {
    el.hoverReadout.textContent = `${bearingLabel(best.bearingDeg)} ${best.bearingDeg.toFixed(0)}° — ${formatPeople(opts.targetPeople)} in ${formatDistance(best.lengthM)}`;
  } else {
    el.hoverReadout.textContent = `${bearingLabel(best.bearingDeg)} ${best.bearingDeg.toFixed(0)}° — still under ${formatPeople(opts.targetPeople)} after ${formatDistance(best.lengthM)} (${formatPeople(best.people)} so far)`;
  }
}

function rayLengths(opts) {
  if (opts.mode === "fixedPeople") {
    return state.rays.map((r) => r.lengthM || 0);
  }
  return scaledLengths(state.rays, opts.lengthM);
}

function tipLatLng(bearingDeg, lengthM) {
  return rosePolygon(state.origin, [{ bearingDeg }], () => lengthM)[0];
}

function drawRose() {
  if (roseLayer) {
    map.removeLayer(roseLayer);
    roseLayer = null;
  }
  if (openLayer) {
    map.removeLayer(openLayer);
    openLayer = null;
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

  if (opts.mode === "fixedPeople") {
    const reachedRays = state.rays.filter((r) => r.reached);
    const openRays = state.rays.filter((r) => !r.reached);
    if (reachedRays.length) {
      const poly = rosePolygon(
        state.origin,
        reachedRays,
        (ray) => lengthByBearing.get(ray.bearingDeg) || 0,
      );
      roseLayer = L.polygon(poly, {
        color: "#d97706",
        weight: 1.5,
        opacity: 0.95,
        fillColor: "#f59e0b",
        fillOpacity: 0.32,
        interactive: true,
      }).addTo(map);
    }
    // Unreached directions: individual dashed spokes out to the search cap.
    if (openRays.length) {
      const lines = openRays.map((r) => [
        [state.origin.lat, state.origin.lon],
        tipLatLng(r.bearingDeg, lengthByBearing.get(r.bearingDeg) || opts.maxLengthM),
      ]);
      openLayer = L.polyline(lines, {
        color: "#64748b",
        weight: 1.25,
        opacity: 0.55,
        dashArray: "5 7",
        interactive: false,
      }).addTo(map);
    }
  } else {
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
  }

  const spokes = [];
  for (const bearing of [0, 90, 180, 270]) {
    const ray = state.rays.reduce((best, r) => {
      const d = Math.abs(r.bearingDeg - bearing);
      const bd = best ? Math.abs(best.bearingDeg - bearing) : 999;
      return d < bd ? r : best;
    }, null);
    const len = ray ? lengthByBearing.get(ray.bearingDeg) || 0 : 0;
    if (!(len > 0)) continue;
    spokes.push([
      [state.origin.lat, state.origin.lon],
      tipLatLng(bearing, len),
    ]);
  }
  spokesLayer = L.polyline(spokes, {
    color: "#92400e",
    weight: 1,
    opacity: 0.5,
    dashArray: "4 6",
    interactive: false,
  }).addTo(map);
}

function fitToRose(opts) {
  if (opts.mode === "fixedPeople") {
    const reached = state.rays.filter((r) => r.reached);
    if (!reached.length) {
      map.setView([state.origin.lat, state.origin.lon], 5, { animate: true });
      return;
    }
    const nearest = Math.min(...reached.map((r) => r.lengthM));
    // Frame the short Manhattan answers tightly; pull back for continental Wyoming ones.
    const fitM =
      nearest < milesToMeters(80)
        ? Math.max(nearest * 3.2, milesToMeters(25))
        : Math.min(Math.max(nearest * 1.1, milesToMeters(200)), milesToMeters(900));
    const tips = [0, 90, 180, 270].map((b) => tipLatLng(b, fitM));
    map.fitBounds(
      L.latLngBounds([[state.origin.lat, state.origin.lon], ...tips]).pad(0.3),
      { animate: true, maxZoom: 11 },
    );
    return;
  }
  const lengths = rayLengths(opts).filter((n) => n > 0);
  if (!lengths.length) return;
  const fitM = Math.max(...lengths);
  const tips = [0, 90, 180, 270].map((b) => tipLatLng(b, fitM));
  map.fitBounds(
    L.latLngBounds([[state.origin.lat, state.origin.lon], ...tips]).pad(0.35),
    { animate: true, maxZoom: 10 },
  );
}

async function recompute({ fit = false } = {}) {
  if (state.busy || !state.grids.length) return;
  const opts = readControls();
  // Small targets (e.g. 100k) use the fine metro tile so petals aren't quantized
  // to ~2 km national cells. Large targets (1M) use CONUS for long rays.
  const grid =
    opts.mode === "fixedPeople"
      ? pickGridForTarget(
          state.grids,
          state.origin.lat,
          state.origin.lon,
          opts.targetPeople,
        )
      : pickGrid(state.grids, state.origin.lat, state.origin.lon, "finest");
  if (!grid) {
    setStatus("Origin is outside the loaded US grid.", "warn");
    state.rays = [];
    drawRose();
    updateHero();
    updateSummary();
    return;
  }
  el.dataset.textContent = `${grid.meta.key || "grid"} · ${grid.meta.note || ""}`;
  state.busy = true;
  setStatus("Tracing lines…");
  await new Promise((r) => setTimeout(r, 0));
  try {
    state.rays = computeRose(grid, state.origin, opts);
    drawRose();
    updateHero();
    updateSummary();
    updateHoverReadout();
    if (fit) fitToRose(opts);
    setStatus("Ready — try Manhattan vs Wyoming, or use My location.", "ok");
  } catch (err) {
    console.error(err);
    setStatus(String(err.message || err), "warn");
  } finally {
    state.busy = false;
  }
}

function setOrigin(lat, lon, { pan = false, fit = false, placeLabel = "" } = {}) {
  state.origin = { lat, lon };
  state.placeLabel = placeLabel;
  originMarker.setLatLng([lat, lon]);
  updateOriginReadout();
  if (pan) map.panTo([lat, lon]);
  recompute({ fit });
}

function goToPlace(key) {
  const place = PLACES[key];
  if (!place) return;
  map.setView([place.lat, place.lon], place.zoom);
  setOrigin(place.lat, place.lon, {
    fit: true,
    placeLabel: place.label,
  });
}

function requestMyLocation() {
  if (!navigator.geolocation) {
    setStatus("Geolocation is not available in this browser.", "warn");
    return;
  }
  el.myLocation.disabled = true;
  setStatus("Requesting your location…");
  navigator.geolocation.getCurrentPosition(
    (pos) => {
      el.myLocation.disabled = false;
      const { latitude: lat, longitude: lon } = pos.coords;
      map.setView([lat, lon], 8);
      setOrigin(lat, lon, { fit: true, placeLabel: "My location" });
    },
    (err) => {
      el.myLocation.disabled = false;
      const msg =
        err.code === err.PERMISSION_DENIED
          ? "Location permission denied."
          : "Could not get your location.";
      setStatus(msg, "warn");
    },
    { enableHighAccuracy: false, timeout: 15_000, maximumAge: 60_000 },
  );
}

function initMap() {
  const start = PLACES.manhattan;
  map = L.map("map", {
    zoomControl: true,
    scrollWheelZoom: true,
  }).setView([start.lat, start.lon], start.zoom);

  L.tileLayer("https://{s}.basemaps.cartocdn.com/light_all/{z}/{x}/{y}{r}.png", {
    attribution:
      '&copy; <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a> &copy; <a href="https://carto.com/attributions">CARTO</a>',
    subdomains: "abcd",
    maxZoom: 18,
  }).addTo(map);

  originMarker = L.marker([start.lat, start.lon], {
    draggable: true,
    title: "Origin",
  }).addTo(map);

  originMarker.on("dragend", () => {
    const ll = originMarker.getLatLng();
    setOrigin(ll.lat, ll.lng, { fit: true, placeLabel: "" });
  });

  map.on("click", (e) => {
    setOrigin(e.latlng.lat, e.latlng.lng, { fit: true, placeLabel: "" });
  });

  map.on("mousemove", (e) => {
    if (!state.rays.length) return;
    const dLat = e.latlng.lat - state.origin.lat;
    const dLon = e.latlng.lng - state.origin.lon;
    const φ = (state.origin.lat * Math.PI) / 180;
    const mLat = 111132.92 - 559.82 * Math.cos(2 * φ);
    const mLon = Math.max(111412.84 * Math.cos(φ), 1);
    const bearing = ((Math.atan2(dLon * mLon, dLat * mLat) * 180) / Math.PI + 360) % 360;
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
        {
          color: best.reached === false ? "#64748b" : "#0f766e",
          weight: 3,
          opacity: 0.9,
          dashArray: best.reached === false ? "6 6" : null,
        },
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
    grids.push(await loadGridFromGzip(meta, buf));
    setStatus(`Loaded ${key}…`);
  }
  state.grids = grids;
  el.dataset.textContent = `${grids.length} grids ready`;
}

function bindControls() {
  el.mode.addEventListener("change", () => {
    syncModeControls();
    recompute({ fit: true });
  });

  // Sliders: live readout; debounced recompute while dragging.
  let sliderTimer = 0;
  for (const slider of [el.lengthMi, el.targetPop]) {
    slider.addEventListener("input", () => {
      syncSliderReadouts();
      clearTimeout(sliderTimer);
      sliderTimer = setTimeout(() => recompute({ fit: false }), 120);
    });
    slider.addEventListener("change", () => {
      clearTimeout(sliderTimer);
      syncSliderReadouts();
      recompute({ fit: true });
    });
  }

  for (const btn of document.querySelectorAll("[data-place]")) {
    btn.addEventListener("click", () => goToPlace(btn.dataset.place));
  }
  el.myLocation.addEventListener("click", requestMyLocation);
  syncModeControls();
  updateOriginReadout();
}

async function main() {
  initMap();
  bindControls();
  try {
    await loadDatasets();
    await recompute({ fit: true });
    const conus = pickGrid(
      state.grids,
      PLACES.manhattan.lat,
      PLACES.manhattan.lon,
      "broadest",
    );
    if (conus) {
      const target = 1_000_000;
      const maxM = milesToMeters(3000);
      const nycDist = distanceToPeople(
        conus,
        PLACES.manhattan,
        28,
        target,
        0,
        maxM,
        { stepM: 1000 },
      );
      const wyDist = distanceToPeople(
        conus,
        PLACES.wyoming,
        84,
        target,
        0,
        maxM,
        { stepM: 1000 },
      );
      console.info(
        `1M people — Manhattan ~NNE: ${formatDistance(nycDist)}, Wyoming ~E: ${formatDistance(wyDist)}`,
      );
    }
  } catch (err) {
    console.error(err);
    setStatus(`Failed to load data: ${err.message || err}`, "warn");
  }
}

main();
