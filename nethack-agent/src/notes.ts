import { LIMITS } from "./limits.js";
import type { Memory } from "./types.js";

const KEY_LETTERS = new Set([..."hjklyubn."]);
const NOT_A_TRACE = new Set(["buy", "bun", "hub", "hum", "nun", "yum", "bub", "nub", "huh"]);

/**
 * Refuse a note that is a log of one screen.
 * A claim that is still true on a different screen passes.
 * The refusal does not name commands.
 */
export function noteRefusal(text: string): string | undefined {
  const collapsed = text.replace(/\s+/g, " ").trim();
  if (!collapsed) return "note is empty";
  if (/^(?:n\d+|t\d+|life\s*\d+|life\d+)\b/i.test(collapsed)) {
    return "a turn log, not a claim that survives this screen";
  }
  if (/\bturn\s+\d+\b/i.test(collapsed)) {
    return "a turn log, not a claim that survives this screen";
  }
  const bare = unquoted(collapsed);
  if (hasKeyTrace(bare) || (bare.match(/\b[a-z]=[a-z]/gi) ?? []).length >= 2) {
    return "a key trace, not a claim that survives this screen";
  }
  if (/\b(?:row|col|column)\s*\d+\b/i.test(bare) || /\br\d+c\d+\b/i.test(bare)) {
    return "a position on this screen, not a claim that survives it";
  }
  if (screenLogScore(bare) >= 2) {
    return "a log of this screen, not a claim that survives it";
  }
  return undefined;
}

/** Drop turn logs, overlong sequences, and picture lines from a loaded notebook. */
export function compactMemory(memory: Memory): { droppedNotes: number; droppedSequences: number } {
  const noteCount = memory.notes.length;
  memory.notes = memory.notes.filter((note) => !note.retracted && !noteRefusal(note.text));
  const ids = memory.notes
    .map((note) => Number(note.id.replace(/^n/, "")))
    .filter((n) => Number.isFinite(n));
  memory.nextNote = ids.length === 0 ? 1 : Math.max(...ids) + 1;

  const live = memory.notes.filter((note) => !note.retracted);
  if (live.length > LIMITS.MAX_LIVE_NOTES) {
    const drop = new Set(live.slice(LIMITS.MAX_LIVE_NOTES).map((note) => note.id));
    memory.notes = memory.notes.filter((note) => !drop.has(note.id));
  }

  const sequenceCount = memory.procedures.length;
  memory.procedures = memory.procedures.filter(
    (procedure) =>
      procedure.keys.length > 0 && procedure.keys.length <= LIMITS.MAX_PROCEDURE_KEYS,
  );
  if (memory.procedures.length > LIMITS.MAX_PROCEDURES) {
    memory.procedures = [...memory.procedures]
      .sort((a, b) => a.keys.length - b.keys.length || a.turn - b.turn)
      .slice(0, LIMITS.MAX_PROCEDURES);
  }

  memory.endings = memory.endings.slice(-LIMITS.MAX_ENDINGS_STORED).map((ending) => ({
    ...ending,
    screen: excerptScreen(ending.screen),
  }));

  return {
    droppedNotes: noteCount - memory.notes.length,
    droppedSequences: sequenceCount - memory.procedures.length,
  };
}

/** Keep words from a final screen. Drop the picture. */
export function excerptScreen(screen: string): string {
  const kept = screen
    .split("\n")
    .map((line) => line.trimEnd())
    .filter((line) => !isPictureLine(line));
  let text = kept.join("\n").trim();
  if (!text) {
    const last = screen
      .split("\n")
      .map((line) => line.trim())
      .filter((line) => line.length > 0)
      .at(-1);
    text = last ?? "";
  }
  if (text.length > LIMITS.MAX_ENDING_CHARS) {
    text = text.slice(0, LIMITS.MAX_ENDING_CHARS).trimEnd();
  }
  return text;
}

function unquoted(text: string): string {
  return text.replace(/"[^"]*"|'[^']*'/g, " ");
}

function hasKeyTrace(text: string): boolean {
  return text.split(/[^A-Za-z.]+/).some((token) => {
    if (token.length < 3) return false;
    const lower = token.toLowerCase();
    if (NOT_A_TRACE.has(lower)) return false;
    return [...lower].every((ch) => KEY_LETTERS.has(ch));
  });
}

function hasMapFragment(text: string): boolean {
  return text.split(/\s+/).some((token) => {
    const core = token.replace(/^[^#.|+\-@]+|[^#.|+\-@]+$/g, "");
    if (core.length < 4) return false;
    const drawing = [...core].filter((ch) => "#.|+-@".includes(ch)).length;
    const letters = [...core].filter((ch) => /[A-Za-z]/.test(ch)).length;
    return drawing >= 3 && letters === 0;
  });
}

function screenLogScore(text: string): number {
  let score = 0;
  if (/(?:^|\s)@\b/.test(text)) score += 1;
  if (/\b(?:mid-room|this room|start room|start-room|east strip|west strip)\b/i.test(text)) {
    score += 2;
  }
  if (/\bturns left\b/i.test(text)) score += 3;
  if (/\b(?:probe|retreat)\b/i.test(text)) score += 2;
  if (hasMapFragment(text)) score += 2;
  if (
    /\bthen\b/i.test(text) &&
    /\b(?:west|east|north|south|door|room|corridor|gap)\b/i.test(text)
  ) {
    score += 2;
  }
  if (/\b\d+\s*->\s*\d+/.test(text)) score += 2;
  if (/\b(?:go|push|flee|leave|walk)\s+(?:west|east|north|south|back)\b/i.test(text)) {
    score += 2;
  }
  if (/\b(?:next|try)\s+(?:west|east|north|south)\b/i.test(text)) score += 2;
  return score;
}

function isPictureLine(line: string): boolean {
  const trimmed = line.trim();
  if (!trimmed) return true;
  const chars = [...trimmed].filter((ch) => ch !== " ");
  if (chars.length < 3) return true;
  const letters = chars.filter((ch) => /[A-Za-z]/.test(ch)).length;
  return letters / chars.length < 0.25;
}
