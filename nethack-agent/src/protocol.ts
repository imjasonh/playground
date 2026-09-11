import { LIMITS } from "./limits.js";
import type { AgentAction } from "./types.js";

const NAME_RE = /^[A-Za-z0-9_-]{1,32}$/;

export type ParseResult =
  | { ok: true; action: AgentAction }
  | { ok: false; error: string };

/** Pull the last JSON object that looks like an action out of a model reply. */
export function parseAction(text: string): ParseResult {
  const objects = extractObjects(text);
  if (objects.length === 0) {
    return { ok: false, error: "no JSON object" };
  }
  for (let i = objects.length - 1; i >= 0; i--) {
    const parsed = asAction(objects[i]);
    if (parsed.ok) return parsed;
  }
  return { ok: false, error: "JSON object is not an action" };
}

function asAction(value: unknown): ParseResult {
  if (!value || typeof value !== "object" || Array.isArray(value)) {
    return { ok: false, error: "action must be an object" };
  }
  const raw = value as Record<string, unknown>;
  const hasField =
    "keys" in raw ||
    "quit" in raw ||
    "note" in raw ||
    "retract" in raw ||
    "save" in raw ||
    "run" in raw;
  if (!hasField) {
    return { ok: false, error: "JSON object is not an action" };
  }

  const quit = raw.quit === true;
  let keys = "";
  if (!quit && raw.keys !== undefined) {
    if (typeof raw.keys !== "string") {
      return { ok: false, error: "keys must be a string" };
    }
    keys = raw.keys;
    if (keys.length > LIMITS.MAX_KEYS_PER_TURN) {
      return {
        ok: false,
        error: `keys longer than ${LIMITS.MAX_KEYS_PER_TURN}`,
      };
    }
    if (hasDisallowedControl(keys)) {
      return { ok: false, error: "keys contain a disallowed control character" };
    }
  }

  let run: string | undefined;
  if (!quit && raw.run !== undefined) {
    if (typeof raw.run !== "string" || !NAME_RE.test(raw.run)) {
      return { ok: false, error: "run must be a saved sequence name" };
    }
    run = raw.run;
  }
  if (run && keys) {
    return { ok: false, error: "send keys or run a saved sequence, not both" };
  }

  let note: string | undefined;
  if (raw.note !== undefined) {
    if (typeof raw.note !== "string") {
      return { ok: false, error: "note must be a string" };
    }
    const collapsed = raw.note.replace(/\s+/g, " ").trim();
    if (!collapsed) {
      return { ok: false, error: "note is empty" };
    }
    if (collapsed.length > LIMITS.MAX_NOTE_CHARS) {
      return { ok: false, error: `note longer than ${LIMITS.MAX_NOTE_CHARS}` };
    }
    note = collapsed;
  }

  let retract: string | undefined;
  if (raw.retract !== undefined) {
    if (typeof raw.retract !== "string" || !/^n[0-9]+$/.test(raw.retract)) {
      return { ok: false, error: "retract must be a note id" };
    }
    retract = raw.retract;
  }

  let save: { name: string; keys: string } | undefined;
  if (raw.save !== undefined) {
    if (!raw.save || typeof raw.save !== "object" || Array.isArray(raw.save)) {
      return { ok: false, error: "save must be an object" };
    }
    const saved = raw.save as Record<string, unknown>;
    if (typeof saved.name !== "string" || !NAME_RE.test(saved.name)) {
      return { ok: false, error: "save.name must be a short name" };
    }
    if (typeof saved.keys !== "string" || saved.keys.length === 0) {
      return { ok: false, error: "save.keys must be a non-empty string" };
    }
    if (saved.keys.length > LIMITS.MAX_PROCEDURE_KEYS) {
      return {
        ok: false,
        error: `save.keys longer than ${LIMITS.MAX_PROCEDURE_KEYS}`,
      };
    }
    if (hasDisallowedControl(saved.keys)) {
      return { ok: false, error: "save.keys contain a disallowed control character" };
    }
    save = { name: saved.name, keys: saved.keys };
  }

  if (!quit && !keys && !run && !note && !retract && !save) {
    return { ok: false, error: "action does nothing" };
  }

  return {
    ok: true,
    action: { keys, quit, note, retract, save, run },
  };
}

/** Allow printable characters, newline, carriage return, and escape. */
function hasDisallowedControl(keys: string): boolean {
  for (const ch of keys) {
    const code = ch.codePointAt(0) ?? 0;
    if (code === 0x1b || code === 0x0a || code === 0x0d || code === 0x09) continue;
    if (code < 0x20 || code === 0x7f) return true;
  }
  return false;
}

function extractObjects(text: string): unknown[] {
  const found: unknown[] = [];
  let i = 0;
  while (i < text.length) {
    if (text[i] !== "{") {
      i += 1;
      continue;
    }
    const end = matchingBrace(text, i);
    if (end < 0) {
      i += 1;
      continue;
    }
    const slice = text.slice(i, end + 1);
    try {
      found.push(JSON.parse(slice));
      // A nested object such as save.keys is part of this action, not a second one.
      i = end + 1;
    } catch {
      i += 1;
    }
  }
  return found;
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
      } else if (ch === '"') {
        inString = false;
      }
      continue;
    }
    if (ch === '"') {
      inString = true;
    } else if (ch === "{") {
      depth += 1;
    } else if (ch === "}") {
      depth -= 1;
      if (depth === 0) return i;
    }
  }
  return -1;
}

/** Line differences only. No labels for what a character means. */
export function screenDiff(prev: string, next: string): string {
  const a = prev.split("\n");
  const b = next.split("\n");
  const n = Math.max(a.length, b.length);
  const lines: string[] = [];
  for (let i = 0; i < n; i++) {
    const left = a[i] ?? "";
    const right = b[i] ?? "";
    if (left !== right) {
      lines.push(`- ${left}`);
      lines.push(`+ ${right}`);
    }
  }
  if (lines.length === 0) return "";
  if (lines.length > 40) {
    return `${lines.slice(0, 40).join("\n")}\n(truncated)`;
  }
  return lines.join("\n");
}
