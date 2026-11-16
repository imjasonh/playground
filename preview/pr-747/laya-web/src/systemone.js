import { formatDecision } from "./calibration.js";
import { collateItems } from "./collate.js";
import { assertPackedOptions, packKev } from "./kev-pack.js";
import { prepareItem } from "./prompt.js";
import { QTYPE_IDS, validateQuestion } from "./questions.js";

export function namedQuestions(questions) {
  if (Array.isArray(questions)) {
    return questions.map((question, index) => [`q${index + 1}`, question]);
  }
  return Object.entries(questions);
}

export async function systemOne({
  session,
  family,
  encode,
  specialIds,
  config,
  state,
  questions,
  kevSpecialIds,
}) {
  const started = now();
  const entries = namedQuestions(questions);
  if (entries.length === 0) {
    throw new Error("systemOne: at least one question is required");
  }
  entries.forEach(([, question]) => validateQuestion(question));

  let usageTokens = 0;
  let rows;
  if (family === "kev") {
    const packed = packKev(
      encode,
      kevSpecialIds,
      state,
      entries.map(([, question]) => question),
    );
    assertPackedOptions(
      packed,
      entries.map(([, question]) => question),
    );
    usageTokens = packed.ids.length;
    rows = await session.runKev(packed);
  } else {
    const items = entries.map(([, question]) => {
      const prepared = prepareItem(
        encode,
        specialIds,
        state,
        question,
        config.max_len,
        config.head_max_len,
      );
      return { ...prepared, qtype: QTYPE_IDS[question.type] };
    });
    const batch = collateItems(items, specialIds.pad);
    usageTokens = batch.tokenCount;
    rows = await session.runLaya(batch);
  }

  const answers = {};
  entries.forEach(([id, question], index) => {
    answers[id] = formatDecision(rows[index].logits, rows[index].action, question, config);
  });
  return {
    model: family,
    answers,
    usage: { input_tokens: usageTokens, output_tokens: 0 },
    latency_ms: Math.round(now() - started),
  };
}

function now() {
  return typeof performance !== "undefined" ? performance.now() : Date.now();
}
