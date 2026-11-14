/** Typed System One questions shared by Laya and Kev. */

export const QUESTION_KINDS = ["choice", "score", "noul"];

export const QTYPE_IDS = { choice: 0, score: 1, noul: 2 };

export function parseOptionLine(line) {
  const trimmed = line.trim();
  const colon = trimmed.indexOf(":");
  if (colon < 0) {
    return { label: trimmed, description: null };
  }
  const label = trimmed.slice(0, colon).trim();
  const description = trimmed.slice(colon + 1).trim();
  return { label, description: description ? description : null };
}

export function linesOf(text) {
  return String(text)
    .split(/\n/)
    .map((line) => line.trim())
    .filter(Boolean);
}

/**
 * Normalize a draft into a validated question.
 * `criteria` for choice is `{label, description}[]` or a label→description map.
 */
export function makeQuestion(kind, instructions, criteria) {
  const ins = typeof instructions === "string" ? instructions : JSON.stringify(instructions);
  const question = { type: kind, instructions: ins, criteria };
  validateQuestion(question);
  return question;
}

export function questionFromDraft(kind, instructions, optionsText) {
  if (kind === "choice") {
    return makeQuestion(
      "choice",
      instructions,
      linesOf(optionsText).map(parseOptionLine),
    );
  }
  if (kind === "score") {
    return makeQuestion("score", instructions, linesOf(optionsText));
  }
  return makeQuestion("noul", instructions);
}

export function validateQuestion(question) {
  if (!QUESTION_KINDS.includes(question?.type)) {
    throw new Error("Question type must be choice, score, or noul.");
  }
  const instructions = String(question.instructions ?? "").trim();
  if (!instructions) {
    throw new Error("Instructions are empty.");
  }
  if (question.type === "choice") {
    const options = choiceOptions(question);
    if (options.length === 0) {
      throw new Error("A choice question needs at least one option.");
    }
    const seen = new Set();
    for (const option of options) {
      if (!option.label) {
        throw new Error("Every option needs a label.");
      }
      if (seen.has(option.label)) {
        throw new Error(`Option labels must be unique (${option.label} repeats).`);
      }
      seen.add(option.label);
    }
  }
  if (question.type === "score") {
    const levels = scoreLevels(question);
    if (levels.length === 0) {
      throw new Error("A score question needs at least one level.");
    }
  }
}

export function choiceOptions(question) {
  const criteria = question.criteria;
  if (Array.isArray(criteria)) {
    return criteria.map((item) => {
      if (typeof item === "string") {
        return { label: item, description: null };
      }
      return { label: item.label, description: item.description ?? null };
    });
  }
  return Object.entries(criteria ?? {}).map(([label, description]) => ({
    label,
    description: description ?? null,
  }));
}

export function scoreLevels(question) {
  return Array.isArray(question.criteria) ? question.criteria.slice() : [];
}

/** Option texts in label-index order. Noul is always [false, true]. */
export function renderOptions(question) {
  if (question.type === "choice") {
    return choiceOptions(question).map((option) =>
      option.description ? `${option.label}: ${option.description}` : option.label,
    );
  }
  if (question.type === "score") {
    return scoreLevels(question).map((level, index) => `level ${index}: ${level}`);
  }
  const criteria = question.criteria ?? {};
  const no = criteria.false || "no, the statement does not hold";
  const yes = criteria.true || "yes, the statement holds";
  return [`false: ${no}`, `true: ${yes}`];
}

export function optionCount(question) {
  return renderOptions(question).length;
}

export function optionLabels(question) {
  if (question.type === "choice") {
    return choiceOptions(question).map((option) => option.label);
  }
  if (question.type === "score") {
    return scoreLevels(question).map((_, index) => String(index));
  }
  return ["false", "true"];
}

/** Python json.dumps(obj, ensure_ascii=False) with ", " / ": " separators. */
export function pyJsonDumps(value) {
  if (value === null || value === undefined) {
    return "null";
  }
  if (typeof value === "string") {
    return JSON.stringify(value);
  }
  if (typeof value === "number") {
    return Number.isInteger(value) ? String(value) : JSON.stringify(value);
  }
  if (typeof value === "boolean") {
    return value ? "true" : "false";
  }
  if (Array.isArray(value)) {
    return "[" + value.map(pyJsonDumps).join(", ") + "]";
  }
  return (
    "{" +
    Object.entries(value)
      .map(([key, item]) => `${JSON.stringify(key)}: ${pyJsonDumps(item)}`)
      .join(", ") +
    "}"
  );
}

export function serializeState(state) {
  return typeof state === "string" ? state : pyJsonDumps(state);
}
