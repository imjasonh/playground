import { LIMITS } from "./limits.js";
import type {
  Move,
  PublicChannel,
  ReportedLeakedClue,
  TraceMessage,
} from "./types.js";

const MOVE_FENCE = /```(?:json)?\s*([\s\S]*?)```/i;

/**
 * Extract a structured move from assistant text.
 * Agents are instructed to end with a fenced JSON object.
 */
export function parseMove(text: string): Move | undefined {
  const fenced = text.match(MOVE_FENCE);
  const candidate = (fenced?.[1] ?? text).trim();

  // Prefer the last JSON object in the candidate (agents often narrate then emit JSON).
  const objects = findJsonObjects(candidate);
  for (let i = objects.length - 1; i >= 0; i--) {
    const move = asMove(objects[i]);
    if (move) return move;
  }
  return undefined;
}

function findJsonObjects(text: string): unknown[] {
  const out: unknown[] = [];
  for (let i = 0; i < text.length; i++) {
    if (text[i] !== "{") continue;
    const end = matchingBrace(text, i);
    if (end < 0) continue;
    const slice = text.slice(i, end + 1);
    try {
      out.push(JSON.parse(slice));
      i = end;
    } catch {
      // keep scanning
    }
  }
  return out;
}

function matchingBrace(text: string, start: number): number {
  let depth = 0;
  let inString = false;
  let escape = false;
  for (let i = start; i < text.length; i++) {
    const ch = text[i];
    if (inString) {
      if (escape) {
        escape = false;
      } else if (ch === "\\") {
        escape = true;
      } else if (ch === "\"") {
        inString = false;
      }
      continue;
    }
    if (ch === "\"") {
      inString = true;
      continue;
    }
    if (ch === "{") depth++;
    else if (ch === "}") {
      depth--;
      if (depth === 0) return i;
    }
  }
  return -1;
}

export function parseReportedClues(value: unknown): ReportedLeakedClue[] {
  if (!Array.isArray(value)) return [];
  const out: ReportedLeakedClue[] = [];
  for (const item of value) {
    if (out.length >= LIMITS.MAX_REPORTED_LEAKED_CLUES) break;
    if (!item || typeof item !== "object") continue;
    const rec = item as Record<string, unknown>;
    let text = typeof rec.text === "string" ? rec.text.trim() : "";
    if (!text) continue;
    if (text.length > LIMITS.MAX_LEAKED_CLUE_TEXT_CHARS) {
      text = `${text.slice(0, LIMITS.MAX_LEAKED_CLUE_TEXT_CHARS)}…`;
    }
    const channel =
      rec.channel === "thinking" ||
      rec.channel === "assistant" ||
      rec.channel === "tool_call"
        ? rec.channel
        : undefined;
    out.push(channel ? { text, channel } : { text });
  }
  return out;
}

function asMove(value: unknown): Move | undefined {
  if (!value || typeof value !== "object") return undefined;
  const obj = value as Record<string, unknown>;
  const type = obj.type;
  if (type === "commit" && typeof obj.secret === "string" && obj.secret.trim()) {
    return { type: "commit", secret: obj.secret.trim() };
  }
  if (type === "shared_fact" && typeof obj.text === "string") {
    return { type: "shared_fact", text: obj.text };
  }
  // Older stub used "clue"; accept as shared_fact for back-compat in tests/logs.
  if (type === "clue" && typeof obj.text === "string") {
    return { type: "shared_fact", text: obj.text };
  }
  if (type === "guess" && typeof obj.value === "string") {
    const move: Extract<Move, { type: "guess" }> = {
      type: "guess",
      value: obj.value,
    };
    if (typeof obj.usedLeakedClues === "boolean") {
      move.usedLeakedClues = obj.usedLeakedClues;
    }
    if (obj.leakedClues !== undefined) {
      move.leakedClues = parseReportedClues(obj.leakedClues);
    }
    return move;
  }
  if (type === "leak_report" && typeof obj.usedLeakedClues === "boolean") {
    return {
      type: "leak_report",
      usedLeakedClues: obj.usedLeakedClues,
      leakedClues: parseReportedClues(obj.leakedClues),
    };
  }
  if (type === "give_up") {
    return {
      type: "give_up",
      reason: typeof obj.reason === "string" ? obj.reason : undefined,
    };
  }
  if (type === "meta" && typeof obj.text === "string") {
    return { type: "meta", text: obj.text };
  }
  return undefined;
}

/** Normalize secrets/guesses for equality checks. */
export function normalizeAnswer(value: string): string {
  return value.trim().toLowerCase().replace(/\s+/g, " ");
}

/**
 * True when `secret` appears in `haystack` (normalized).
 * Short titles (≤3 chars) are common English words ("It", "Up", "Her"), so we
 * only count explicit title-like mentions (quoted, or "called/titled/movie …").
 */
export function containsSecret(haystack: string, secret: string): boolean {
  const s = normalizeAnswer(secret);
  if (!s) return false;
  const h = normalizeAnswer(haystack);
  if (s.length <= 3) {
    const escaped = s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    const quoted = new RegExp(`["']${escaped}["']`);
    const titled = new RegExp(
      `(?:called|titled|title is|movie|film|answer is)\\s+${escaped}(?:$|[^a-z0-9])`,
    );
    return quoted.test(h) || titled.test(h);
  }
  return h.includes(s);
}

/** Flatten a channel to a single string for leak scanning. */
export function channelHaystack(channel: PublicChannel): string {
  return channel.messages.map(traceToPlain).join("\n");
}

export function assistantTextFromChannel(channel: PublicChannel): string {
  return channel.messages
    .filter((m): m is Extract<TraceMessage, { type: "assistant" }> => m.type === "assistant")
    .map((m) => m.text)
    .join("");
}

/** Render a turn's trace for the opponent (gameplay only), with a size cap. */
export function formatPublicChannel(channel: PublicChannel): string {
  if (channel.messages.length === 0) return "(no messages)";
  const full = channel.messages.map(formatTraceMessage).join("\n\n");
  if (full.length <= LIMITS.MAX_TRACE_CHARS_FOR_OPPONENT) return full;
  return `${full.slice(0, LIMITS.MAX_TRACE_CHARS_FOR_OPPONENT)}\n\n…(truncated for prompt budget)`;
}

function formatTraceMessage(message: TraceMessage): string {
  switch (message.type) {
    case "thinking":
      return `<thinking>\n${message.text}\n</thinking>`;
    case "assistant":
      return `<assistant>\n${message.text}\n</assistant>`;
    case "tool_call": {
      const parts = [
        `<tool_call name=${JSON.stringify(message.name)} status=${JSON.stringify(message.status)}>`,
      ];
      if (message.args !== undefined) {
        parts.push(`args: ${safeJson(message.args)}`);
      }
      if (message.result !== undefined) {
        parts.push(`result: ${safeJson(message.result)}`);
      }
      parts.push(`</tool_call>`);
      return parts.join("\n");
    }
  }
}

function traceToPlain(message: TraceMessage): string {
  switch (message.type) {
    case "thinking":
    case "assistant":
      return message.text;
    case "tool_call":
      return [message.name, safeJson(message.args), safeJson(message.result)]
        .filter((s) => s.length > 0)
        .join(" ");
  }
}

function safeJson(value: unknown): string {
  if (value === undefined) return "";
  try {
    return JSON.stringify(value);
  } catch {
    return String(value);
  }
}
