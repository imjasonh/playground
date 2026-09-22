import { optionLabels, QTYPE_IDS } from "./questions.js";

export function softmax(values) {
  if (values.length === 0) {
    return [];
  }
  let max = values[0];
  for (const value of values) {
    if (value > max) {
      max = value;
    }
  }
  const exps = values.map((value) => Math.exp(value - max));
  const total = exps.reduce((sum, value) => sum + value, 0);
  return exps.map((value) => value / total);
}

export function sizeBucket(k) {
  if (k <= 2) {
    return "2";
  }
  if (k <= 5) {
    return "3-5";
  }
  if (k <= 10) {
    return "6-10";
  }
  return "11+";
}

export function tempBucket(kind, k) {
  return `${kind}:${sizeBucket(k)}`;
}

export function temperatureScale(calibration, kind, optionCount) {
  const byOptions = calibration.temperatureByOptions ?? calibration.temperature_by_options ?? {};
  const key = tempBucket(kind, optionCount);
  if (Object.hasOwn(byOptions, key)) {
    return byOptions[key];
  }
  const index = QTYPE_IDS[kind];
  const list = calibration.temperature ?? [1, 1, 1];
  return index < list.length ? list[index] : 1;
}

/** `1 - H(p) / log(k)`, clipped to `[0, 1]`. */
export function confidenceFromProbs(probabilities, k = probabilities.length) {
  if (k < 2) {
    return 1;
  }
  let entropy = 0;
  for (let i = 0; i < k; i += 1) {
    const p = probabilities[i];
    entropy -= p * Math.log(Math.min(Math.max(p, 1e-12), 1));
  }
  return Math.min(Math.max(1 - entropy / Math.log(k), 0), 1);
}

export function round4(value) {
  return Math.round(value * 10000) / 10000;
}

/**
 * Turn marker logits into a System One answer.
 * Noul confidence is `max(p, 1 - p)`, matching the Playground iOS runtime.
 */
export function formatDecision(logits, action, question, calibration = {}) {
  const k = optionLabels(question).length;
  if (k < 1 || logits.length < k) {
    throw new Error(`Model returned ${logits.length} logits for ${k} options.`);
  }
  if (!logits.every(Number.isFinite) || !action.every(Number.isFinite)) {
    throw new Error("Non-finite model outputs");
  }
  const act = softmax(action.map(Number));
  const scale = Math.max(1e-3, temperatureScale(calibration, question.type, k));
  const p = softmax(logits.slice(0, k).map((value) => Number(value) / scale));
  const labels = optionLabels(question);
  let confidence = round4(confidenceFromProbs(p, k));
  let answer;
  if (question.type === "choice") {
    let best = 0;
    for (let i = 1; i < p.length; i += 1) {
      if (p[i] > p[best]) {
        best = i;
      }
    }
    answer = {
      type: "choice",
      choice: labels[best],
      probabilities: Object.fromEntries(labels.map((label, i) => [label, round4(p[i])])),
      confidence,
      act_probability: round4(act[0] ?? 0),
    };
  } else if (question.type === "score") {
    const score = p.reduce((sum, value, i) => sum + i * value, 0);
    answer = {
      type: "score",
      score: round4(score),
      legend: Object.fromEntries(labels.map((label, i) => [label, question.criteria[i]])),
      probabilities: Object.fromEntries(p.map((value, i) => [String(i), round4(value)])),
      confidence,
      act_probability: round4(act[0] ?? 0),
    };
  } else {
    const yes = p[1] ?? 0;
    confidence = round4(Math.max(yes, 1 - yes));
    answer = {
      type: "noul",
      noul: round4(yes),
      confidence,
      act_probability: round4(act[0] ?? 0),
    };
  }
  return answer;
}
