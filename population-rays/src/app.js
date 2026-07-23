// Leaflet UI: distance-to-N corridor rose.

import {
  bearingLabel,
  feetToMeters,
  formatDistance,
  formatPeople,
  milesToMeters,
} from "./geo.js";
import { searchUsPlaces } from "./geocode.js";
import { loadGridFromGzip, gridsForRose } from "./grid.js";
import { computeRose, rosePolygon } from "./rays.js";

const PLACES = {
  manhattan: {
    lat: 40.758,
    lon: -73.9855,
    zoom: 9,
    label: "Manhattan",
  },
  wyoming: {
    lat: 43.076,
    lon: -107.2903,
    zoom: 6,
    label: "Wyoming",
  },
};

const RAY_COUNT = 72; // 5°
const MAX_SEARCH_MI = 3000;
const CORRIDOR_WIDTH_FT = 100;
const CORRIDOR_WIDTH_M = feetToMeters(CORRIDOR_WIDTH_FT);

const el = {
  status: document.getElementById("status"),
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
  const targetPeople = Number(el.targetPop.value) || 100_000;
  return {
    widthM: CORRIDOR_WIDTH_M,
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
  const opts = readControls();
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

function drawRose() {
  if (roseLayer) map.removeLayer(roseLayer);
  if (openLayer) map.removeLayer(openLayer);
  if (spokesLayer) map.removeLayer(spokesLayer);
  roseLayer = openLayer = spokesLayer = null;
  if (!state.rays.length) return;

  const reachedRays = state.rays.filter((r) => r.reached);

  // Build the rose from every bearing. Unreached tips collapse to the origin
  // so we get real petals — never a polygon that only connects far tip points
  // (which floated as a giant blob over the SE when sparse origins only hit
  // N in a few directions).
  if (reachedRays.length) {
    roseLayer = L.polygon(
      rosePolygon(state.origin, state.rays, (ray) =>
        ray.reached ? ray.lengthM : 0,
      ),
      {
        color: "#d97706",
        weight: 1.5,
        opacity: 0.95,
        fillColor: "#f59e0b",
        fillOpacity: 0.32,
      },
    ).addTo(map);
  }

  // Unreached bearings: short dashed ticks at the rose scale (not 3000 mi spokes).
  if (reachedRays.length && reachedRays.length < state.rays.length) {
    const tickM = Math.max(
      ...reachedRays.map((r) => r.lengthM),
      milesToMeters(50),
    );
    openLayer = L.polyline(
      state.rays
        .filter((r) => !r.reached)
        .map((r) => [
          [state.origin.lat, state.origin.lon],
          tipLatLng(r.bearingDeg, tickM * 1.08),
        ]),
      {
        color: "#64748b",
        weight: 1.25,
        opacity: 0.45,
        dashArray: "5 7",
        interactive: false,
      },
    ).addTo(map);
  }

  const spokes = [];
  for (const bearing of [0, 90, 180, 270]) {
    const { ray } = nearestRay(bearing);
    if (!ray.reached || !(ray.lengthM > 0)) continue;
    spokes.push([
      [state.origin.lat, state.origin.lon],
      tipLatLng(bearing, ray.lengthM),
    ]);
  }
  if (spokes.length) {
    spokesLayer = L.polyline(spokes, {
      color: "#92400e",
      weight: 1,
      opacity: 0.45,
      dashArray: "4 6",
      interactive: false,
    }).addTo(map);
  }
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

async function recompute({ fit = false } = {}) {
  if (state.busy || !state.grids.length) return;
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
  state.busy = true;
  setStatus("Computing…");
  await new Promise((r) => setTimeout(r, 0));
  try {
    state.rays = computeRose(grids, state.origin, opts);
    drawRose();
    updateHero();
    updateHoverReadout();
    if (fit) fitToRose();
    setStatus("Ready", "ok");
  } catch (err) {
    console.error(err);
    setStatus(String(err.message || err), "warn");
  } finally {
    state.busy = false;
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
  map = L.map("map", { zoomControl: true, scrollWheelZoom: true }).setView(
    [start.lat, start.lon],
    start.zoom,
  );

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
}

async function loadDatasets() {
  setStatus("Loading…");
  const index = await (await fetch("data/index.json")).json();
  const grids = [];
  for (const key of index.datasets) {
    const meta = await (await fetch(`data/${key}.json`)).json();
    const buf = new Uint8Array(await (await fetch(`data/${meta.file}`)).arrayBuffer());
    grids.push(await loadGridFromGzip(meta, buf));
  }
  state.grids = grids;
}

function bindControls() {
  let timer = 0;
  el.targetPop.addEventListener("input", () => {
    syncSliderReadouts();
    clearTimeout(timer);
    timer = setTimeout(() => recompute({ fit: false }), 120);
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
  try {
    await loadDatasets();
    await recompute({ fit: true });
  } catch (err) {
    console.error(err);
    setStatus(`Failed: ${err.message || err}`, "warn");
  }
}

main();
