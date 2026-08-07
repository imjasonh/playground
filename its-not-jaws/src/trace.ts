import { parseMove } from "./protocol.js";
import type { TraceMessage } from "./types.js";

/**
 * Merge consecutive same-type stream chunks into one thinking / assistant /
 * tool_call message so transcripts read as continuous prose.
 */
export function coalesceTraceMessages(messages: TraceMessage[]): TraceMessage[] {
  const out: TraceMessage[] = [];
  for (const message of messages) {
    const prev = out[out.length - 1];
    if (
      prev &&
      prev.type === message.type &&
      (message.type === "thinking" || message.type === "assistant")
    ) {
      const merged = joinStreamChunks([
        (prev as { text: string }).text,
        message.text,
      ]);
      out[out.length - 1] = { type: message.type, text: merged };
      continue;
    }
    if (
      prev &&
      prev.type === "tool_call" &&
      message.type === "tool_call" &&
      prev.name === message.name
    ) {
      out[out.length - 1] = {
        type: "tool_call",
        name: message.name,
        status: message.status || prev.status,
        args: message.args !== undefined ? message.args : prev.args,
        result: message.result !== undefined ? message.result : prev.result,
      };
      continue;
    }
    out.push({ ...message });
  }
  return out;
}

/**
 * Join token stream chunks. Cursor SDK deltas already include any leading
 * spaces; do not invent separators (that turns "Titan"+"ic" into "Titan ic").
 */
export function joinStreamChunks(chunks: string[]): string {
  return chunks.join("");
}

/**
 * Remove protocol move JSON (fenced or trailing bare object) from assistant
 * speech. The structured move is shown separately in the UI.
 */
export function stripMoveFences(text: string): string {
  let out = text.replace(/```(?:json)?\s*([\s\S]*?)```/gi, (full, body: string) => {
    if (parseMove(full) || parseMove(body)) return "";
    return full;
  });

  // Trailing bare JSON move (some models omit fences).
  out = out.replace(/\s*(\{[\s\S]*\})\s*$/u, (full, body: string) => {
    return parseMove(body) ? "" : full;
  });

  return out.replace(/[ \t]+\n/g, "\n").replace(/\n{3,}/g, "\n\n").trim();
}

/** Visible assistant speech after coalescing + stripping move JSON. */
export function assistantSpeech(messages: TraceMessage[]): string {
  const coalesced = coalesceTraceMessages(messages);
  return coalesced
    .filter((m): m is Extract<TraceMessage, { type: "assistant" }> => m.type === "assistant")
    .map((m) => stripMoveFences(m.text))
    .filter(Boolean)
    .join("\n\n")
    .trim();
}
