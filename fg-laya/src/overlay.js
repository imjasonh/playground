/**
 * Per-tick decision overlay. Turns System One answers plus the surfaces
 * written this tick into a banner the HUD and FlightGear can show.
 */

const SURFACES = ["aileron", "elevator", "throttle", "rudder"];

const SHORT = {
  aileron: "AIL",
  elevator: "ELE",
  throttle: "THR",
  rudder: "RUD",
};

export function buildOverlay({
  ticks = 0,
  answers = {},
  controls = {},
  target = {},
  backend = "local",
  model = "",
  latency_ms = 0,
} = {}) {
  const rows = SURFACES.map((surface) => overlayRow(surface, answers[surface], controls, target));
  return {
    tick: Number(ticks) || 0,
    backend,
    model,
    latency_ms: Number(latency_ms) || 0,
    rows,
    banner: formatBanner(Number(ticks) || 0, rows),
  };
}

export function overlayRow(surface, answer = {}, controls = {}, target = {}) {
  const choice = choiceOf(answer);
  const confidence = confidenceOf(answer, choice);
  return {
    surface,
    short: SHORT[surface] ?? surface.slice(0, 3).toUpperCase(),
    choice,
    confidence,
    applied: finiteNumber(controls[surface]),
    target: finiteNumber(target[surface]),
    line: formatRow(SHORT[surface] ?? surface, choice, controls[surface], confidence),
  };
}

export function formatBanner(tick, rows) {
  const body = (rows ?? []).map((row) => row.line).join("  ");
  return `tick|${tick}  ${body}`;
}

export function formatRow(shortName, choice, applied, confidence) {
  const n = finiteNumber(applied);
  const value = n == null ? "-" : n.toFixed(2);
  const pct = Number.isFinite(confidence) ? `${Math.round(confidence * 100)}pct` : "";
  // FlightGear's HUD font drops ordinary spaces, so keep the tokens
  // readable if they get concatenated.
  return [shortName, choice, value, pct].filter(Boolean).join("|");
}

export function overlayPropertyWrites(overlay) {
  if (!overlay) {
    return [];
  }
  const writes = [
    ["/laya/overlay/banner", overlay.banner],
    ["/laya/overlay/tick", `tick|${overlay.tick}`],
  ];
  for (const row of overlay.rows ?? []) {
    writes.push([`/laya/overlay/${row.surface}`, row.line]);
  }
  return writes;
}

function choiceOf(answer) {
  if (!answer) {
    return "—";
  }
  if (answer.type === "noul") {
    return Number(answer.noul) >= 0.5 ? "yes" : "no";
  }
  if (answer.choice != null && answer.choice !== "") {
    return String(answer.choice);
  }
  if (answer.score != null) {
    return String(answer.score);
  }
  return "—";
}

function confidenceOf(answer, choice) {
  if (!answer) {
    return null;
  }
  if (answer.type === "noul") {
    const p = Number(answer.noul);
    return Number.isFinite(p) ? p : null;
  }
  const fromLabel = answer.probabilities?.[choice];
  if (Number.isFinite(fromLabel)) {
    return fromLabel;
  }
  const conf = Number(answer.confidence);
  return Number.isFinite(conf) ? conf : null;
}

function finiteNumber(value) {
  const n = Number(value);
  return Number.isFinite(n) ? n : null;
}
