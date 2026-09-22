import { optionCount, renderOptions, serializeState } from "./questions.js";

/** Qwen unused special tokens Kev reuses as delimiters. */
export const KEV_SPECIAL = {
  state: "<|fim_prefix|>",
  question: "<|fim_middle|>",
  optOpen: "<|box_start|>",
  optClose: "<|box_end|>",
  decide: "<|fim_suffix|>",
};

export const OPT_NONE = -1;
export const OPT_DECIDE = -2;

export const MAX_STATE = 384;
export const MAX_BRANCH = 1024;
export const MAX_PACKED = 2048;

const SPECIAL_RE = /<\|([A-Za-z0-9_]+)\|>/g;

/** Rewrite delimiter-shaped spans so user text cannot forge option boundaries. */
export function escapeUserText(text) {
  return String(text).replace(SPECIAL_RE, "<¦$1¦>");
}

/**
 * Pack one System One record the way Kev's `encode()` does.
 *
 * `[<state> …state…]` then per question `[<q> instr <opt> opt </opt> … <decide>]`.
 */
export function packKev(encode, specialIds, state, questions, limits = {}) {
  const maxState = limits.maxState ?? MAX_STATE;
  const maxBranch = limits.maxBranch ?? MAX_BRANCH;
  const maxPacked = limits.maxPacked ?? MAX_PACKED;
  const optionIsolation = Boolean(limits.optionIsolation);

  const stateTokens = encode(escapeUserText(serializeState(state)));
  const stateIds = [specialIds.state, ...stateTokens.slice(0, maxState - 1)];
  const ids = stateIds.slice();
  const seg = Array(stateIds.length).fill(0);
  const pos = stateIds.map((_, index) => index);
  const opt = Array(stateIds.length).fill(OPT_NONE);
  const decideIdx = [];
  const optIdx = [];

  const items = Array.isArray(questions) ? questions : Object.values(questions);
  items.forEach((question, index) => {
    const k = index + 1;
    const instr = [specialIds.question, ...encode(escapeUserText(question.instructions))];
    const spans = renderOptions(question).map((option) => [
      specialIds.optOpen,
      ...encode(escapeUserText(option)),
      specialIds.optClose,
    ]);
    const branch = [...instr, ...spans.flat(), specialIds.decide];
    if (branch.length > maxBranch - stateIds.length) {
      throw new Error(`branch too long: ${branch.length}`);
    }
    const base = ids.length;
    const p0 = stateIds.length;
    const branchOpt = [
      ...Array(instr.length).fill(OPT_NONE),
      ...spans.flatMap((span, optionIndex) => Array(span.length).fill(optionIndex)),
      OPT_DECIDE,
    ];
    let branchPos;
    if (optionIsolation) {
      const longest = Math.max(...spans.map((span) => span.length));
      branchPos = [
        ...instr.map((_, i) => p0 + i),
        ...spans.flatMap((span) => span.map((_, i) => p0 + instr.length + i)),
        p0 + instr.length + longest,
      ];
    } else {
      branchPos = branch.map((_, i) => p0 + i);
    }
    const ends = [];
    let cursor = instr.length;
    for (const span of spans) {
      cursor += span.length;
      ends.push(cursor - 1);
    }
    ids.push(...branch);
    seg.push(...Array(branch.length).fill(k));
    pos.push(...branchPos);
    opt.push(...branchOpt);
    decideIdx.push(base + branch.length - 1);
    optIdx.push(ends.map((end) => base + end));
  });

  if (ids.length > maxPacked) {
    throw new Error(`packed sequence is ${ids.length} tokens; max is ${maxPacked}`);
  }
  return {
    ids,
    seg,
    pos,
    opt,
    optionIsolation,
    decideIdx,
    optIdx,
    stateTruncated: stateTokens.length + 1 > maxState,
  };
}

export function kevRows(encoding) {
  const stateLength = encoding.seg.filter((value) => value === 0).length;
  const rows = [];
  let start = stateLength;
  encoding.decideIdx.forEach((decide, index) => {
    const end = decide + 1;
    const k = index + 1;
    if (encoding.seg[start] !== k || encoding.seg[end - 1] !== k) {
      throw new Error("branch layout mismatch");
    }
    rows.push({
      ids: encoding.ids.slice(start, end),
      pos: encoding.pos.slice(start, end),
      decide: decide - start,
      opts: encoding.optIdx[index].map((offset) => offset - start),
    });
    start = end;
  });
  return {
    stateIds: encoding.ids.slice(0, stateLength),
    statePos: encoding.pos.slice(0, stateLength),
    rows,
  };
}

export function assertPackedOptions(encoding, questions) {
  const items = Array.isArray(questions) ? questions : Object.values(questions);
  items.forEach((question, index) => {
    if (encoding.optIdx[index].length !== optionCount(question)) {
      throw new Error("Too many options for the token budget.");
    }
  });
}
