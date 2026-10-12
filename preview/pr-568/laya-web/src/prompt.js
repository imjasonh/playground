import { optionCount, renderOptions, serializeState } from "./questions.js";

export const OPTION_TOKEN_CAP = 48;

/**
 * Laya sequence layout from the Python runtime:
 * [CLS] <type> question: <instructions> [SEP] [MASK] opt0 [MASK] opt1 … [SEP] <state> [SEP]
 */
export function buildPrefix(encode, ids, question, headMaxLength = 192) {
  const maskTok = ids.maskTok;
  const options = renderOptions(question);
  const instructions = String(question.instructions).split(maskTok).join(" ");
  let headIds = encode(`${question.type} question: ${instructions}`);

  let optionIds = options.map((option) => {
    const text = " " + option.split(maskTok).join(" ");
    return [ids.mask, ...encode(text).slice(0, OPTION_TOKEN_CAP)];
  });

  const total = (rows) => rows.reduce((sum, row) => sum + row.length, 0);
  let optionBudget = headMaxLength - total(optionIds);
  if (optionBudget < 16) {
    const per = Math.max(4, Math.floor((headMaxLength - 16) / Math.max(1, optionIds.length)));
    optionIds = optionIds.map((row) => row.slice(0, per));
    optionBudget = headMaxLength - total(optionIds);
  }
  headIds = headIds.slice(0, Math.max(8, optionBudget));

  const seq = [ids.cls, ...headIds, ids.sep];
  const markers = [];
  for (const row of optionIds) {
    markers.push(seq.length);
    seq.push(...row);
  }
  seq.push(ids.sep);
  return { ids: seq, markers };
}

export function buildSequence(encode, ids, state, question, maxLength = 512, headMaxLength = 192) {
  const { ids: seq, markers } = buildPrefix(encode, ids, question, headMaxLength);
  const room = Math.max(0, maxLength - seq.length - 1);
  const stateText = serializeState(state).split(ids.maskTok).join(" ");
  seq.push(...encode(stateText).slice(0, room), ids.sep);
  const trimmed = seq.slice(0, maxLength);
  return {
    ids: trimmed,
    markers: markers.filter((marker) => marker < maxLength),
  };
}

export function prepareItem(encode, ids, state, question, maxLength, headMaxLength) {
  const built = buildSequence(encode, ids, state, question, maxLength, headMaxLength);
  if (built.markers.length !== optionCount(question)) {
    throw new Error("Too many options for the token budget.");
  }
  return { ...built, kind: question.type };
}
