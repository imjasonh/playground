import { clamp } from "./geo.js";
import { choiceLabels, optionLabels, scoreLevels, validateQuestion } from "./questions.js";

const OPENROUTER_DECISIONS = "https://openrouter.ai/api/alpha/decisions";
const DEFAULT_JEV_MODEL = "typesafe/jev-1.13";

/**
 * Answer every question. `local` always works. `jev` posts to OpenRouter's
 * Decisions API when OPENROUTER_API_KEY is set. `laya` posts to a local
 * System One HTTP server (the same JSON body as Jev).
 */
export async function askSystemOne(state, questions, options = {}) {
  const backend = options.backend ?? detectBackend();
  const entries = Object.entries(questions);
  if (entries.length === 0) {
    throw new Error("askSystemOne: at least one question is required");
  }
  entries.forEach(([, question]) => validateQuestion(question));

  if (backend === "jev") {
    return askJev(state, questions, options);
  }
  if (backend === "laya") {
    return askLayaHttp(state, questions, options);
  }
  return askLocal(state, questions);
}

export function detectBackend() {
  if (process.env.SYSTEMONE_BACKEND) {
    return process.env.SYSTEMONE_BACKEND;
  }
  if (process.env.OPENROUTER_API_KEY) {
    return "jev";
  }
  if (process.env.LAYA_URL) {
    return "laya";
  }
  return "local";
}

export function askLocal(state, questions) {
  const started = now();
  const answers = {};
  for (const [id, question] of Object.entries(questions)) {
    answers[id] = answerLocal(state, id, question);
  }
  return {
    model: "local-systemone",
    backend: "local",
    answers,
    latency_ms: Math.round(now() - started),
  };
}

export async function askJev(state, questions, options = {}) {
  const apiKey = options.apiKey ?? process.env.OPENROUTER_API_KEY;
  if (!apiKey) {
    throw new Error("Jev needs OPENROUTER_API_KEY");
  }
  const started = now();
  const body = {
    model: options.model ?? process.env.JEV_MODEL ?? DEFAULT_JEV_MODEL,
    state,
    questions,
  };
  const response = await fetch(options.url ?? OPENROUTER_DECISIONS, {
    method: "POST",
    headers: {
      Authorization: `Bearer ${apiKey}`,
      "Content-Type": "application/json",
      "HTTP-Referer": "https://github.com/imjasonh/playground",
      "X-OpenRouter-Title": "fg-laya",
    },
    body: JSON.stringify(body),
    signal: AbortSignal.timeout(options.timeout_ms ?? 4000),
  });
  if (!response.ok) {
    const text = await response.text();
    throw new Error(`Jev HTTP ${response.status}: ${text.slice(0, 400)}`);
  }
  const payload = await response.json();
  return {
    model: payload.model ?? body.model,
    backend: "jev",
    answers: payload.answers,
    usage: payload.usage,
    latency_ms: Math.round(now() - started),
  };
}

export async function askLayaHttp(state, questions, options = {}) {
  const url = options.layaUrl ?? process.env.LAYA_URL;
  if (!url) {
    throw new Error("Laya needs LAYA_URL");
  }
  const started = now();
  const response = await fetch(url, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ state, questions }),
    signal: AbortSignal.timeout(options.timeout_ms ?? 4000),
  });
  if (!response.ok) {
    const text = await response.text();
    throw new Error(`Laya HTTP ${response.status}: ${text.slice(0, 400)}`);
  }
  const payload = await response.json();
  return {
    model: payload.model ?? "laya",
    backend: "laya",
    answers: payload.answers,
    usage: payload.usage,
    latency_ms: Math.round(now() - started),
  };
}

/**
 * Local System One. Same question types and answer shapes as Jev/Laya.
 * Logits come from the instrument feelings on `state`, then softmax. This is
 * the backend the demo uses when no Jev key or Laya graph is on the machine.
 */
export function answerLocal(state, id, question) {
  if (question.type === "noul") {
    const p = noulProbability(state, id);
    return { type: "noul", noul: p, confidence: Math.max(p, 1 - p) };
  }
  if (question.type === "score") {
    const levels = scoreLevels(question);
    const logits = levels.map((_, index) => scoreLogit(state, id, index, levels.length));
    const probabilities = softmax(logits);
    const score = probabilities.reduce((sum, p, index) => sum + p * index, 0);
    const legend = Object.fromEntries(levels.map((label, index) => [String(index), label]));
    return {
      type: "score",
      score,
      probabilities: Object.fromEntries(probabilities.map((p, index) => [String(index), p])),
      legend,
      confidence: Math.max(...probabilities),
    };
  }
  const labels = choiceLabels(question);
  const logits = labels.map((label) => choiceLogit(state, id, label));
  const probabilities = softmax(logits);
  const best = argMax(probabilities);
  return {
    type: "choice",
    choice: labels[best],
    probabilities: Object.fromEntries(labels.map((label, index) => [label, probabilities[index]])),
    confidence: probabilities[best],
  };
}

function choiceLogit(state, id, label) {
  if (id === "aileron") {
    return aileronLogit(state, label);
  }
  if (id === "elevator") {
    return elevatorLogit(state, label);
  }
  if (id === "throttle") {
    return throttleLogit(state, label);
  }
  if (id === "rudder") {
    return rudderLogit(state, label);
  }
  return 0;
}

function aileronLogit(state, label) {
  const headingErr = Number(state.heading_err_deg) || 0;
  const roll = Number(state.roll_deg) || 0;
  const desiredBank = clamp(headingErr * 0.75, -30, 30);
  const bankErr = desiredBank - roll;
  const overbank = Math.abs(roll) > 32;
  switch (label) {
    case "left-hard":
      return (bankErr < -12 ? 4.2 : -1.2) + (overbank && roll > 0 ? 2 : 0);
    case "left":
      return (bankErr < -4 ? 3.4 : bankErr < 0 ? 1.2 : -0.8) + (roll > 20 ? 1.4 : 0);
    case "level":
      return Math.abs(bankErr) < 5 ? 3.6 : Math.abs(bankErr) < 10 ? 1.5 : -1.5;
    case "right":
      return (bankErr > 4 ? 3.4 : bankErr > 0 ? 1.2 : -0.8) + (roll < -20 ? 1.4 : 0);
    case "right-hard":
      return (bankErr > 12 ? 4.2 : -1.2) + (overbank && roll < 0 ? 2 : 0);
    default:
      return 0;
  }
}

function elevatorLogit(state, label) {
  const altErr = Number(state.altitude_err_ft) || 0;
  const speedErr = Number(state.airspeed_err_kt) || 0;
  const pitch = Number(state.pitch_deg) || 0;
  const stall = (Number(state.airspeed_kt) || 100) < 65;
  const desiredPitch = clamp(-altErr / 220 + speedErr / 18, -8, 9);
  const pitchErr = desiredPitch - pitch;
  if (stall) {
    if (label === "down-hard") return 5;
    if (label === "down") return 2.5;
    return -2;
  }
  switch (label) {
    case "down-hard":
      return pitchErr < -6 || pitch > 12 || altErr > 500 ? 4 : -1.4;
    case "down":
      return pitchErr < -1.5 ? 3.2 : pitchErr < 0 ? 1 : -0.7;
    case "hold":
      return Math.abs(pitchErr) < 1.4 && Math.abs(altErr) < 180 ? 3.8 : -0.6;
    case "up":
      return pitchErr > 1.5 && !stall ? 3.2 : pitchErr > 0 ? 1 : -0.7;
    case "up-hard":
      return pitchErr > 6 && altErr < -400 && !stall ? 4 : -1.4;
    default:
      return 0;
  }
}

function throttleLogit(state, label) {
  const speedErr = Number(state.airspeed_err_kt) || 0;
  const climb = (Number(state.vsi_fpm) || 0) > 400;
  switch (label) {
    case "cut":
      return speedErr > 14 ? 4 : -1.5;
    case "less":
      return speedErr > 4 ? 3.3 : speedErr > 0 ? 0.8 : -0.8;
    case "hold":
      return Math.abs(speedErr) < 4 ? 3.7 : -0.4;
    case "more":
      return speedErr < -4 || (climb && speedErr < 0) ? 3.3 : speedErr < 0 ? 0.8 : -0.8;
    case "full":
      return speedErr < -12 ? 4 : -1.5;
    default:
      return 0;
  }
}

function rudderLogit(state, label) {
  const slip = Number(state.slip_deg) || 0;
  const roll = Number(state.roll_deg) || 0;
  const want = clamp(roll * 0.04 - slip, -1, 1);
  switch (label) {
    case "left":
      return want < -0.15 ? 3 : -0.6;
    case "center":
      return Math.abs(want) < 0.2 ? 3.4 : 0.2;
    case "right":
      return want > 0.15 ? 3 : -0.6;
    default:
      return 0;
  }
}

function noulProbability(state, id) {
  if (id === "arrived") {
    const dist = Number(state.waypoint?.distance_nm);
    if (!Number.isFinite(dist)) {
      return 0.05;
    }
    if (dist <= 0.25) return 0.92;
    if (dist <= 0.4) return 0.7;
    if (dist <= 0.6) return 0.28;
    return 0.06;
  }
  return 0.5;
}

function scoreLogit(state, id, index, count) {
  const t = count <= 1 ? 0 : index / (count - 1);
  if (id === "energy") {
    const speedErr = Number(state.airspeed_err_kt) || 0;
    const want = clamp((speedErr + 15) / 30, 0, 1);
    return -((t - want) ** 2) * 8;
  }
  return 0;
}

export function softmax(logits) {
  const max = Math.max(...logits);
  const exps = logits.map((x) => Math.exp(x - max));
  const sum = exps.reduce((a, b) => a + b, 0);
  return exps.map((x) => x / sum);
}

function argMax(values) {
  let best = 0;
  for (let i = 1; i < values.length; i++) {
    if (values[i] > values[best]) {
      best = i;
    }
  }
  return best;
}

function now() {
  return typeof performance !== "undefined" ? performance.now() : Date.now();
}

export function emptyControls() {
  return { aileron: 0, elevator: 0, rudder: 0, throttle: 0.7 };
}

export { optionLabels };
