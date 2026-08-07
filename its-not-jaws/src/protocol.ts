import type { Move, PublicChannel, TraceMessage } from "./types.js";

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

function asMove(value: unknown): Move | undefined {
  if (!value || typeof value !== "object") return undefined;
  const obj = value as Record<string, unknown>;
  const type = obj.type;
  if (type === "commit" && typeof obj.secret === "string" && obj.secret.trim()) {
    return { type: "commit", secret: obj.secret.trim() };
  }
  if (type === "clue" && typeof obj.text === "string") {
    return { type: "clue", text: obj.text };
  }
  if (type === "guess" && typeof obj.value === "string") {
    return { type: "guess", value: obj.value };
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
 * True when `secret` appears as a contiguous normalized substring of `haystack`.
 * Used for leak detection against published gameplay traces.
 */
export function containsSecret(haystack: string, secret: string): boolean {
  if (!secret.trim()) return false;
  return normalizeAnswer(haystack).includes(normalizeAnswer(secret));
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

/** Render a turn's full trace for the opponent (gameplay only). */
export function formatPublicChannel(channel: PublicChannel): string {
  if (channel.messages.length === 0) return "(no messages)";
  return channel.messages.map(formatTraceMessage).join("\n\n");
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
