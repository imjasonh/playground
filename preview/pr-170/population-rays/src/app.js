// Leaflet UI: distance-to-N corridor rose.

import {
  bearingLabel,
  destination,
  formatDistance,
  formatPeople,
  milesToMeters,
} from "./geo.js";
import { searchUsPlaces } from "./geocode.js";
import { loadGridFromGzip, gridsForRose } from "./grid.js";
import { computeRoseAsync, DEFAULT_SLICE_DEG, rosePolygon } from "./rays.js";

const PLACES = {
  manhattan: {
    lat: 40.758,
    lon: -73.9855,
    zoom: 9,
    label: "Manhattan",
  },
  "manhattan-ks": {
    lat: 39.1836,
    lon: -96.5717,
    zoom: 7,
    label: "Manhattan, KS",
  },
  "manhattan-il": {
    lat: 41.4223,
    lon: -87.9859,
    zoom: 8,
    label: "Manhattan, IL",
  },
};

const RAY_COUNT = 72; // every 5°
const SLICE_DEG = DEFAULT_SLICE_DEG; // filled pie slice; tiles the rose
const MAX_SEARCH_MI = 3000;

const el = {
  status: document.getElementById("status"),
  mapStatus: document.getElementById("map-status"),
  targetPop: document.getElementById("target-pop"),
  targetReadout: document.getElementById("target-pop-readout"),
  ledeN: document.getElementById("lede-n"),
  hoverReadout: document.getElementById("hover-readout"),
  myLocation: document.getElementById("my-location"),
  heroValue: document.getElementById("hero-value"),
  heroDetail: document.getElementById("hero-detail"),
  placeForm: document.getElementById("place-search-form"),
  placeSearch: document.getElementById("place-search"),
  placeResults: document.getElementById("place-results"),
  searchGo: document.querySelector(".search-go"),
};

const state = {
  grids: [],
  origin: { ...PLACES.manhattan },
  rays: [],
  busy: false,
  hoverBearing: null,
  computeGen: 0,
};

let map;
let originMarker;
let roseLayer;
let openLayer;
let hoverLine;

function setStatus(text, kind = "") {
  el.status.textContent = text;
  el.status.dataset.kind = kind;
  if (!el.mapStatus) return;
  // Keep the on-map chip for progress/errors (sidebar status is easy to miss
  // on phones). Idle "Ready" stays in the sidebar; the map shows the legend.
  if (kind === "ok") return;
  el.mapStatus.textContent = text;
  el.mapStatus.dataset.kind = kind;
  el.mapStatus.hidden = !text;
}

function setMapHint(text) {
  if (!el.mapStatus) return;
  el.mapStatus.textContent = text;
  el.mapStatus.dataset.kind = "";
  el.mapStatus.hidden = !text;
}

function readControls() {
  const targetPeople = Number(el.targetPop.value) || 100_000;
  return {
    sliceDeg: SLICE_DEG,
    targetPeople,
    maxLengthM: milesToMeters(MAX_SEARCH_MI),
    rayCount: RAY_COUNT,
  };
}

function syncSliderReadouts() {
  const n = formatPeople(readControls().targetPeople);
  el.targetReadout.textContent = n;
  el.ledeN.textContent = n;
}

function updateHero() {
  const opts = readControls();
  if (!state.rays.length) {
    el.heroValue.textContent = "—";
    el.heroDetail.textContent = "Pick a place or click the map.";
    return;
  }
  const reached = state.rays.filter((r) => r.reached);
  if (!reached.length) {
    el.heroValue.textContent = `>${MAX_SEARCH_MI} mi`;
    el.heroDetail.textContent = `No direction hits ${formatPeople(opts.targetPeople)} within ${MAX_SEARCH_MI} mi.`;
    return;
  }
  let nearest = reached[0];
  for (const r of reached) if (r.lengthM < nearest.lengthM) nearest = r;
  el.heroValue.textContent = formatDistance(nearest.lengthM);
  el.heroDetail.textContent = `${bearingLabel(nearest.bearingDeg)} → ${formatPeople(opts.targetPeople)}`;
}

function nearestRay(bearing) {
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
  return { ray: best, diff: bestDiff };
}

function updateHoverReadout() {
  if (state.hoverBearing == null || !state.rays.length) {
    el.hoverReadout.textContent = "";
    return;
  }
  const step = 360 / state.rays.length;
  const { ray, diff } = nearestRay(state.hoverBearing);
  if (diff > step) {
    el.hoverReadout.textContent = "";
    return;
  }
  if (ray.reached) {
    el.hoverReadout.textContent = `${bearingLabel(ray.bearingDeg)} ${ray.bearingDeg.toFixed(0)}° · ${formatDistance(ray.lengthM)}`;
  } else {
    el.hoverReadout.textContent = `${bearingLabel(ray.bearingDeg)} ${ray.bearingDeg.toFixed(0)}° · not reached (${formatPeople(ray.people)} in ${MAX_SEARCH_MI} mi)`;
  }
}

function tipLatLng(bearingDeg, lengthM) {
  return rosePolygon(state.origin, [{ bearingDeg }], () => lengthM)[0];
}

/** LatLng at bearing/distance from the current origin. */
function atBearing(bearingDeg, lengthM) {
  const p = destination(
    state.origin.lat,
    state.origin.lon,
    bearingDeg,
    lengthM,
  );
  return [p.lat, p.lon];
}

/**
 * Contiguous runs of unreached bearings, as [startIdx, endIdx] inclusive.
 * Handles wrap-around (e.g. last + first both open).
 */
function unreachedRuns(rays) {
  const n = rays.length;
  if (!n) return [];
  const open = rays.map((r) => !r.reached);
  if (!open.some(Boolean)) return [];
  if (open.every(Boolean)) return [[0, n - 1]];

  /** @type {[number, number][]} */
  const runs = [];
  let i = 0;
  while (i < n) {
    if (!open[i]) {
      i += 1;
      continue;
    }
    let j = i;
    while (j + 1 < n && open[j + 1]) j += 1;
    runs.push([i, j]);
    i = j + 1;
  }
  // Merge a trailing run with a leading run across 0°.
  if (runs.length >= 2 && runs[0][0] === 0 && runs[runs.length - 1][1] === n - 1) {
    const head = runs.shift();
    const tail = runs.pop();
    runs.push([tail[0], head[1]]);
  }
  return runs;
}

/** Angular edges of an inclusive ray-index run (wrap-aware). */
function runBearingEdges(rays, startIdx, endIdx) {
  const n = rays.length;
  const step = 360 / n;
  if (startIdx <= endIdx) {
    return {
      left: rays[startIdx].bearingDeg - step / 2,
      right: rays[endIdx].bearingDeg + step / 2,
    };
  }
  // Wrapped: startIdx..n-1 and 0..endIdx
  return {
    left: rays[startIdx].bearingDeg - step / 2,
    right: rays[endIdx].bearingDeg + step / 2 + 360,
  };
}

/** Closed ring for an annular sector from bearing left→right (right may be >360). */
function sectorRing(leftDeg, rightDeg, rInner, rOuter) {
  const span = rightDeg - leftDeg;
  const samples = Math.max(2, Math.ceil(Math.abs(span) / 4));
  /** @type {[number, number][]} */
  const outer = [];
  /** @type {[number, number][]} */
  const inner = [];
  for (let s = 0; s <= samples; s++) {
    const b = leftDeg + (span * s) / samples;
    outer.push(atBearing(b, rOuter));
    if (rInner > 0) inner.push(atBearing(b, rInner));
  }
  if (rInner <= 0) {
    return [[state.origin.lat, state.origin.lon], ...outer];
  }
  return [...inner, ...outer.reverse()];
}

/**
 * Soft “beyond max search” fan: solid near the pin, fading to transparent at
 * MAX_SEARCH_MI so the cutoff reads as “farther than this,” not a hard rim.
 */
function drawOpenSlices(group, rays) {
  const maxM = milesToMeters(MAX_SEARCH_MI);
  const BANDS = 14;
  const FADE_START = 0.5; // outer half fades
  const BASE_FILL = 0.26;

  for (const [startIdx, endIdx] of unreachedRuns(rays)) {
    const { left, right } = runBearingEdges(rays, startIdx, endIdx);
    for (let b = 0; b < BANDS; b++) {
      const t0 = b / BANDS;
      const t1 = (b + 1) / BANDS;
      const r0 = t0 * maxM;
      const r1 = t1 * maxM;
      const tMid = (t0 + t1) / 2;
      const fade =
        tMid <= FADE_START
          ? 1
          : Math.max(0, 1 - (tMid - FADE_START) / (1 - FADE_START));
      const fillOpacity = BASE_FILL * fade * fade;
      if (fillOpacity < 0.01) continue;

      L.polygon(sectorRing(left, right, r0, r1), {
        stroke: b === 0,
        color: "#3d5a6c",
        weight: b === 0 ? 1 : 0,
        opacity: 0.35,
        fillColor: "#5b7c99",
        fillOpacity,
        interactive: false,
      }).addTo(group);
    }
  }
}

function drawReachedSlices(group, rays) {
  const half = SLICE_DEG / 2;
  for (const ray of rays) {
    if (!ray.reached || !(ray.lengthM > 0)) continue;
    const left = ray.bearingDeg - half;
    const right = ray.bearingDeg + half;
    L.polygon(sectorRing(left, right, 0, ray.lengthM), {
      color: "#d97706",
      weight: 1,
      opacity: 0.9,
      fillColor: "#f59e0b",
      fillOpacity: 0.34,
      interactive: false,
    }).addTo(group);
  }
}

function drawRose() {
  if (roseLayer) map.removeLayer(roseLayer);
  if (openLayer) map.removeLayer(openLayer);
  roseLayer = openLayer = null;
  if (!state.rays.length) return;

  const reachedRays = state.rays.filter((r) => r.reached);
  const hasOpen = reachedRays.length < state.rays.length;

  // Unreached fans under the amber slices (slate → transparent at 3000 mi).
  if (hasOpen) {
    openLayer = L.layerGroup().addTo(map);
    drawOpenSlices(openLayer, state.rays);
  }

  if (reachedRays.length) {
    roseLayer = L.layerGroup().addTo(map);
    drawReachedSlices(roseLayer, state.rays);
  }

  invalidateMap();
}

function fitToRose() {
  const reached = state.rays.filter((r) => r.reached);
  if (!reached.length) {
    map.setView([state.origin.lat, state.origin.lon], 5, { animate: true });
    return;
  }
  const nearest = Math.min(...reached.map((r) => r.lengthM));
  const fitM =
    nearest < milesToMeters(80)
      ? Math.max(nearest * 3.2, milesToMeters(25))
      : Math.min(Math.max(nearest * 1.1, milesToMeters(200)), milesToMeters(900));
  const tips = [0, 90, 180, 270].map((b) => tipLatLng(b, fitM));
  map.fitBounds(
    L.latLngBounds([[state.origin.lat, state.origin.lon], ...tips]).pad(0.3),
    { animate: true, maxZoom: 11 },
  );
}

function invalidateMap() {
  if (!map) return;
  map.invalidateSize({ animate: false });
}

async function recompute({ fit = false } = {}) {
  if (!state.grids.length) return;
  const opts = readControls();
  const grids = gridsForRose(
    state.grids,
    state.origin.lat,
    state.origin.lon,
  );
  if (!grids.length) {
    setStatus("Outside the US grid.", "warn");
    state.rays = [];
    drawRose();
    updateHero();
    return;
  }

  const gen = ++state.computeGen;
  state.busy = true;
  setStatus("Computing petals…");
  try {
    const rays = await computeRoseAsync(grids, state.origin, opts, (done, total) => {
      if (gen !== state.computeGen) return;
      setStatus(`Computing… ${done}/${total}`);
    });
    if (gen !== state.computeGen) return;
    state.rays = rays;
    drawRose();
    updateHero();
    updateHoverReadout();
    if (fit) fitToRose();
    const n = formatPeople(opts.targetPeople);
    setStatus("Ready", "ok");
    const anyOpen = state.rays.some((r) => !r.reached);
    setMapHint(
      anyOpen
        ? `Amber hits ${n} · slate fades past ${MAX_SEARCH_MI} mi`
        : `Petals hit ${n}`,
    );
  } catch (err) {
    if (gen !== state.computeGen) return;
    console.error(err);
    setStatus(String(err.message || err), "warn");
  } finally {
    if (gen === state.computeGen) state.busy = false;
  }
}

function setOrigin(lat, lon, { fit = false } = {}) {
  state.origin = { lat, lon };
  originMarker.setLatLng([lat, lon]);
  recompute({ fit });
}

function goToPlace(key) {
  const place = PLACES[key];
  if (!place) return;
  clearPlaceResults();
  el.placeSearch.value = place.label;
  map.setView([place.lat, place.lon], place.zoom);
  setOrigin(place.lat, place.lon, { fit: true });
}

function goToSearchHit(hit) {
  clearPlaceResults();
  el.placeSearch.value = hit.label.split(",")[0] || hit.label;
  map.setView([hit.lat, hit.lon], hit.zoom);
  setOrigin(hit.lat, hit.lon, { fit: true });
}

function clearPlaceResults() {
  el.placeResults.hidden = true;
  el.placeResults.innerHTML = "";
}

function showPlaceResults(hits, { emptyMessage } = {}) {
  el.placeResults.innerHTML = "";
  if (!hits.length) {
    const li = document.createElement("li");
    li.className = "place-empty";
    li.textContent = emptyMessage || "No US places found.";
    el.placeResults.appendChild(li);
    el.placeResults.hidden = false;
    return;
  }
  for (const hit of hits) {
    const li = document.createElement("li");
    li.setAttribute("role", "option");
    const btn = document.createElement("button");
    btn.type = "button";
    btn.textContent = hit.label;
    btn.addEventListener("click", () => goToSearchHit(hit));
    li.appendChild(btn);
    el.placeResults.appendChild(li);
  }
  el.placeResults.hidden = false;
}

let searchAbort = null;
let searchTimer = 0;

async function runPlaceSearch(query, { autoSelectSingle = false } = {}) {
  const q = String(query || "").trim();
  if (q.length < 2) {
    clearPlaceResults();
    return;
  }
  if (searchAbort) searchAbort.abort();
  searchAbort = new AbortController();
  const { signal } = searchAbort;
  el.searchGo.disabled = true;
  setStatus("Searching…");
  try {
    const hits = await searchUsPlaces(q, { signal, limit: 5 });
    if (signal.aborted) return;
    if (autoSelectSingle && hits.length === 1) {
      goToSearchHit(hits[0]);
      setStatus("Ready", "ok");
      return;
    }
    showPlaceResults(hits, {
      emptyMessage: "No contiguous-US places found.",
    });
    setStatus(hits.length ? "Ready" : "No places found.", hits.length ? "ok" : "warn");
  } catch (err) {
    if (err?.name === "AbortError") return;
    console.error(err);
    showPlaceResults([], { emptyMessage: "Search failed. Try again." });
    setStatus("Search failed.", "warn");
  } finally {
    el.searchGo.disabled = false;
  }
}

function bindPlaceSearch() {
  el.placeForm.addEventListener("submit", (e) => {
    e.preventDefault();
    clearTimeout(searchTimer);
    runPlaceSearch(el.placeSearch.value, { autoSelectSingle: true });
  });
  el.placeSearch.addEventListener("input", () => {
    clearTimeout(searchTimer);
    const q = el.placeSearch.value;
    if (String(q).trim().length < 2) {
      clearPlaceResults();
      return;
    }
    searchTimer = setTimeout(() => runPlaceSearch(q), 350);
  });
  el.placeSearch.addEventListener("keydown", (e) => {
    if (e.key === "Escape") clearPlaceResults();
  });
}

function requestMyLocation() {
  if (!navigator.geolocation) {
    setStatus("Location unavailable.", "warn");
    return;
  }
  el.myLocation.disabled = true;
  setStatus("Locating…");
  navigator.geolocation.getCurrentPosition(
    (pos) => {
      el.myLocation.disabled = false;
      map.setView([pos.coords.latitude, pos.coords.longitude], 8);
      setOrigin(pos.coords.latitude, pos.coords.longitude, { fit: true });
    },
    (err) => {
      el.myLocation.disabled = false;
      setStatus(
        err.code === err.PERMISSION_DENIED
          ? "Location denied."
          : "Location failed.",
        "warn",
      );
    },
    { enableHighAccuracy: false, timeout: 15_000, maximumAge: 60_000 },
  );
}

function initMap() {
  const start = PLACES.manhattan;
  map = L.map("map", {
    zoomControl: true,
    scrollWheelZoom: true,
    preferCanvas: false,
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
    setOrigin(ll.lat, ll.lng, { fit: true });
  });
  map.on("click", (e) => setOrigin(e.latlng.lat, e.latlng.lng, { fit: true }));

  map.on("mousemove", (e) => {
    if (!state.rays.length) return;
    const dLat = e.latlng.lat - state.origin.lat;
    const dLon = e.latlng.lng - state.origin.lon;
    const φ = (state.origin.lat * Math.PI) / 180;
    const mLat = 111132.92 - 559.82 * Math.cos(2 * φ);
    const mLon = Math.max(111412.84 * Math.cos(φ), 1);
    const bearing =
      ((Math.atan2(dLon * mLon, dLat * mLat) * 180) / Math.PI + 360) % 360;
    state.hoverBearing = bearing;
    updateHoverReadout();

    const step = 360 / state.rays.length;
    const { ray, diff } = nearestRay(bearing);
    if (hoverLine) map.removeLayer(hoverLine);
    if (diff > step * 1.5) return;
    const reached = state.rays.filter((r) => r.reached);
    const hoverLen = ray.reached
      ? ray.lengthM
      : reached.length
        ? Math.max(...reached.map((r) => r.lengthM)) * 1.08
        : milesToMeters(100);
    if (!(hoverLen > 0)) return;
    hoverLine = L.polyline(
      [
        [state.origin.lat, state.origin.lon],
        tipLatLng(ray.bearingDeg, hoverLen),
      ],
      {
        color: ray.reached ? "#0f766e" : "#64748b",
        weight: 3,
        opacity: 0.9,
        dashArray: ray.reached ? null : "6 6",
      },
    ).addTo(map);
  });

  // Mobile Safari often initializes the map before the stacked layout has a
  // real height; without this the SVG overlay never shows even when tiles do.
  const onResize = () => invalidateMap();
  window.addEventListener("resize", onResize);
  window.addEventListener("orientationchange", onResize);
  if (window.visualViewport) {
    window.visualViewport.addEventListener("resize", onResize);
  }
  requestAnimationFrame(() => {
    invalidateMap();
    requestAnimationFrame(invalidateMap);
  });
}

async function loadOneDataset(key) {
  const meta = await (await fetch(`data/${key}.json`)).json();
  const buf = new Uint8Array(
    await (await fetch(`data/${meta.file}`)).arrayBuffer(),
  );
  return loadGridFromGzip(meta, buf);
}

/**
 * Load grids (Northeast before bulky CONUS). Recompute after each new covering
 * tile; the rose always picks the finest covering grid, so NYC petals do not
 * change shape when CONUS arrives — only places outside the metro tile gain a
 * rose once CONUS lands.
 */
async function loadDatasets() {
  const index = await (await fetch("data/index.json")).json();
  const keys = [...index.datasets].sort((a, b) => {
    const rank = (k) => (k.includes("northeast") ? 0 : 1);
    return rank(a) - rank(b);
  });

  for (let i = 0; i < keys.length; i++) {
    setStatus(
      keys.length > 1
        ? `Loading map data… ${i + 1}/${keys.length}`
        : "Loading map data…",
    );
    const grid = await loadOneDataset(keys[i]);
    const idx = state.grids.findIndex((g) => g.meta.key === grid.meta.key);
    if (idx >= 0) state.grids[idx] = grid;
    else state.grids.push(grid);

    if (
      gridsForRose(state.grids, state.origin.lat, state.origin.lon).length
    ) {
      await recompute({ fit: i === 0 });
    }
  }
}

function bindControls() {
  let timer = 0;
  el.targetPop.addEventListener("input", () => {
    syncSliderReadouts();
    clearTimeout(timer);
    // Debounce heavily while dragging — each rose can take hundreds of ms and
    // overlapping gens still paint intermediate N values that look "erratic".
    timer = setTimeout(() => recompute({ fit: false }), 200);
  });
  el.targetPop.addEventListener("change", () => {
    clearTimeout(timer);
    syncSliderReadouts();
    recompute({ fit: true });
  });
  for (const btn of document.querySelectorAll("[data-place]")) {
    btn.addEventListener("click", () => goToPlace(btn.dataset.place));
  }
  el.myLocation.addEventListener("click", requestMyLocation);
  bindPlaceSearch();
  syncSliderReadouts();
}

async function main() {
  initMap();
  bindControls();
  setStatus("Loading map data…");
  try {
    await loadDatasets();
    await recompute({ fit: true });
  } catch (err) {
    console.error(err);
    setStatus(`Failed: ${err.message || err}`, "warn");
  }
}

main();
