const $ = (id) => document.getElementById(id);
const overlayOnly = new URLSearchParams(location.search).get("mode") === "overlay";
if (overlayOnly) {
  document.body.classList.add("overlay-only");
}

const horizon = $("horizon");
const map = $("map");
const hz = horizon.getContext("2d");
const mz = map.getContext("2d");
let lastChoices = {};

const source = new EventSource("/stream");
source.onmessage = (event) => {
  const frame = JSON.parse(event.data);
  renderTickOverlay(frame);
  if (overlayOnly) {
    return;
  }
  renderMeta(frame);
  renderTapes(frame.aircraft);
  drawHorizon(frame.aircraft);
  drawMap(frame);
  renderDecisions(frame.answers);
};

function renderTickOverlay(frame) {
  const overlay = frame.overlay;
  const root = $("tick-overlay");
  $("tick-num").textContent = String(overlay?.tick ?? frame.ticks ?? 0);
  $("tick-meta").textContent =
    `${frame.backend}${frame.model ? ` · ${frame.model}` : ""} · ` +
    `applied this tick · ${frame.latency_ms ?? 0} ms`;
  const rows = $("tick-rows");
  rows.replaceChildren();
  for (const row of overlay?.rows ?? []) {
    const changed = lastChoices[row.surface] != null && lastChoices[row.surface] !== row.choice;
    lastChoices[row.surface] = row.choice;
    const card = document.createElement("div");
    card.className = "tick-row" + (changed ? " is-changed" : "");
    const surface = document.createElement("div");
    surface.className = "tick-surface";
    surface.textContent = row.surface;
    const choice = document.createElement("div");
    choice.className = "tick-choice";
    choice.textContent = row.choice;
    const applied = document.createElement("div");
    applied.className = "tick-applied";
    applied.textContent = Number.isFinite(row.applied) ? row.applied.toFixed(2) : "—";
    const p = document.createElement("div");
    p.className = "tick-p";
    p.textContent = Number.isFinite(row.confidence)
      ? `${Math.round(row.confidence * 100)}%`
      : "";
    card.append(surface, choice, applied, p);
    rows.append(card);
  }
  root.classList.remove("is-fresh");
  void root.offsetWidth;
  root.classList.add("is-fresh");
}

function renderMeta(frame) {
  const a = frame.aircraft;
  $("meta").textContent =
    `${frame.backend} · ${frame.model ?? ""} · ${frame.world} · ${frame.mission} · ` +
    `${a.lat.toFixed(3)}, ${a.lon.toFixed(3)} · ${frame.latency_ms} ms`;
}

function renderTapes(a) {
  $("ias").textContent = `${a.airspeed_kt.toFixed(0)} kt`;
  $("alt").textContent = `${a.altitude_ft.toFixed(0)} ft`;
  $("hdg").textContent = `${a.heading_deg.toFixed(0).padStart(3, "0")}°`;
  $("vsi").textContent = `${a.vsi_fpm >= 0 ? "+" : ""}${a.vsi_fpm.toFixed(0)}`;
}

function drawHorizon(a) {
  const w = horizon.width;
  const h = horizon.height;
  const cx = w / 2;
  const cy = h / 2;
  hz.save();
  hz.clearRect(0, 0, w, h);
  hz.translate(cx, cy);
  hz.rotate((-a.roll_deg * Math.PI) / 180);
  const pitchPx = a.pitch_deg * 6;
  hz.fillStyle = "#6f92a8";
  hz.fillRect(-w, -h * 2 - pitchPx, w * 2, h * 2);
  hz.fillStyle = "#6a5a3a";
  hz.fillRect(-w, -pitchPx, w * 2, h * 2);
  hz.strokeStyle = "rgba(255,255,255,0.45)";
  hz.lineWidth = 1;
  for (let p = -20; p <= 20; p += 5) {
    const y = -p * 6 - pitchPx;
    const len = p === 0 ? 80 : 28;
    hz.beginPath();
    hz.moveTo(-len, y);
    hz.lineTo(len, y);
    hz.stroke();
  }
  hz.restore();
  hz.strokeStyle = "#b6d36a";
  hz.lineWidth = 3;
  hz.beginPath();
  hz.moveTo(cx - 46, cy);
  hz.lineTo(cx - 12, cy);
  hz.moveTo(cx + 12, cy);
  hz.lineTo(cx + 46, cy);
  hz.moveTo(cx, cy);
  hz.arc(cx, cy, 4, 0, Math.PI * 2);
  hz.stroke();
}

function drawMap(frame) {
  const w = map.width;
  const h = map.height;
  mz.fillStyle = "#0d100c";
  mz.fillRect(0, 0, w, h);
  const trail = frame.trail ?? [];
  const center = frame.nav.center ?? frame.aircraft;
  const scale = 95 / Math.max(0.8, frame.nav.radius_nm ?? 2);
  const proj = (p) => {
    const dx = (p.lon - center.lon) * 60 * Math.cos((center.lat * Math.PI) / 180);
    const dy = (p.lat - center.lat) * 60;
    return [w / 2 + dx * scale, h / 2 - dy * scale];
  };
  if (frame.mission === "circle") {
    mz.strokeStyle = "#2c3428";
    mz.beginPath();
    const r = (frame.nav.radius_nm ?? 1.6) * scale;
    mz.arc(w / 2, h / 2, r, 0, Math.PI * 2);
    mz.stroke();
  }
  mz.strokeStyle = "#b6d36a";
  mz.lineWidth = 2;
  mz.beginPath();
  trail.forEach((p, i) => {
    const [x, y] = proj(p);
    if (i === 0) mz.moveTo(x, y);
    else mz.lineTo(x, y);
  });
  mz.stroke();
  const [ax, ay] = proj(frame.aircraft);
  mz.save();
  mz.translate(ax, ay);
  mz.rotate((frame.aircraft.heading_deg * Math.PI) / 180);
  mz.fillStyle = "#e8ecdf";
  mz.beginPath();
  mz.moveTo(0, -10);
  mz.lineTo(7, 9);
  mz.lineTo(0, 5);
  mz.lineTo(-7, 9);
  mz.closePath();
  mz.fill();
  mz.restore();
  if (frame.nav.waypoint && frame.mission === "waypoints") {
    const [wx, wy] = proj(frame.nav.waypoint);
    mz.fillStyle = "#e0c36a";
    mz.beginPath();
    mz.arc(wx, wy, 4, 0, Math.PI * 2);
    mz.fill();
  }
}

function renderDecisions(answers) {
  const root = $("decisions");
  root.replaceChildren();
  for (const [name, answer] of Object.entries(answers ?? {})) {
    const q = document.createElement("div");
    q.className = "q";
    const title = document.createElement("div");
    title.className = "q-name";
    title.textContent = name;
    const body = document.createElement("div");
    if (answer.type === "noul") {
      body.append(bar("yes", answer.noul ?? 0, answer.noul >= 0.5));
    } else if (answer.probabilities) {
      for (const [label, p] of Object.entries(answer.probabilities)) {
        const win = answer.choice === label || String(answer.score) === label;
        body.append(bar(label, p, win));
      }
    }
    q.append(title, body);
    root.append(q);
  }
}

function bar(label, p, win) {
  const row = document.createElement("div");
  row.className = "bar-row" + (win ? " is-win" : "");
  const lbl = document.createElement("span");
  lbl.className = "lbl";
  lbl.textContent = label;
  const track = document.createElement("div");
  track.className = "track";
  const fill = document.createElement("div");
  fill.className = "fill";
  fill.style.width = `${Math.round((p ?? 0) * 100)}%`;
  track.append(fill);
  const pct = document.createElement("span");
  pct.className = "pct";
  pct.textContent = `${Math.round((p ?? 0) * 100)}%`;
  row.append(lbl, track, pct);
  return row;
}
