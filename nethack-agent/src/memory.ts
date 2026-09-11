import { mkdir, readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { LIMITS } from "./limits.js";
import { excerptScreen, noteRefusal } from "./notes.js";
import type { AgentAction, Ending, Memory, Note, Procedure } from "./types.js";

export function emptyMemory(): Memory {
  return { notes: [], procedures: [], endings: [], nextNote: 1 };
}

export async function loadMemory(dir: string): Promise<Memory> {
  const memory = emptyMemory();
  const notes = await readJson<Note[]>(path.join(dir, "notes.json"));
  const procedures = await readJson<Procedure[]>(path.join(dir, "procedures.json"));
  const endings = await readJson<Ending[]>(path.join(dir, "endings.json"));
  if (notes) memory.notes = notes;
  if (procedures) memory.procedures = procedures;
  if (endings) memory.endings = endings;
  const ids = memory.notes
    .map((note) => Number(note.id.replace(/^n/, "")))
    .filter((n) => Number.isFinite(n));
  memory.nextNote = ids.length === 0 ? 1 : Math.max(...ids) + 1;
  return memory;
}

export async function saveMemory(dir: string, memory: Memory): Promise<void> {
  await mkdir(dir, { recursive: true });
  await writeFile(path.join(dir, "notes.json"), JSON.stringify(memory.notes, null, 2));
  await writeFile(
    path.join(dir, "procedures.json"),
    JSON.stringify(memory.procedures, null, 2),
  );
  await writeFile(
    path.join(dir, "endings.json"),
    JSON.stringify(memory.endings, null, 2),
  );
}

export type MemoryAck = {
  ack?: string;
  error?: string;
};

export type NotebookBudget = {
  notesAdded: number;
  addedIds: string[];
};

/** Apply notebook fields. Does not send keys. A refused note does not block keys. */
export function applyNotebook(
  memory: Memory,
  action: AgentAction,
  life: number,
  turn: number,
  budget?: NotebookBudget,
): string[] {
  const acks: string[] = [];
  if (action.retract) {
    const note = memory.notes.find((item) => item.id === action.retract);
    if (!note) {
      acks.push(`unknown note ${action.retract}`);
    } else if (!note.retracted) {
      note.retracted = true;
      if (budget) {
        const index = budget.addedIds.indexOf(note.id);
        if (index >= 0) {
          budget.addedIds.splice(index, 1);
          budget.notesAdded = Math.max(0, budget.notesAdded - 1);
        }
      }
      acks.push(`retracted ${note.id}`);
    } else {
      acks.push(`already retracted ${note.id}`);
    }
  }
  if (action.note) {
    const reason = noteRefusal(action.note);
    const live = memory.notes.filter((note) => !note.retracted).length;
    if (reason) {
      acks.push(`note not stored: ${reason}`);
    } else if (budget && budget.notesAdded >= LIMITS.MAX_NOTES_PER_LIFE) {
      acks.push(
        `note not stored: this attempt already filed ${LIMITS.MAX_NOTES_PER_LIFE} notes; retract one first`,
      );
    } else if (live >= LIMITS.MAX_LIVE_NOTES) {
      acks.push("note not stored: notebook is full; retract a note first");
    } else {
      const note: Note = {
        id: `n${memory.nextNote}`,
        life,
        turn,
        text: action.note,
        retracted: false,
      };
      memory.nextNote += 1;
      memory.notes.push(note);
      if (budget) {
        budget.notesAdded += 1;
        budget.addedIds.push(note.id);
      }
      acks.push(`stored note ${note.id}`);
    }
  }
  if (action.save) {
    const existing = memory.procedures.find((item) => item.name === action.save?.name);
    if (!existing && memory.procedures.length >= LIMITS.MAX_PROCEDURES) {
      acks.push("sequence not stored: sequence list is full; save over a name you already have");
    } else if (action.save) {
      const procedure: Procedure = {
        name: action.save.name,
        keys: action.save.keys,
        life,
        turn,
      };
      if (existing) {
        existing.keys = procedure.keys;
        existing.life = life;
        existing.turn = turn;
        acks.push(`replaced sequence ${procedure.name}`);
      } else {
        memory.procedures.push(procedure);
        acks.push(`stored sequence ${procedure.name}`);
      }
    }
  }
  return acks;
}

export function lookupProcedure(memory: Memory, name: string): Procedure | undefined {
  return memory.procedures.find((item) => item.name === name);
}

export function recordEnding(memory: Memory, ending: Ending): void {
  memory.endings.push({ ...ending, screen: excerptScreen(ending.screen) });
  const extra = memory.endings.length - LIMITS.MAX_ENDINGS_STORED;
  if (extra > 0) memory.endings.splice(0, extra);
}

/** Render the agent's own records. Omit commentary about what to do with them. */
export function renderMemory(memory: Memory): string {
  const sections: string[] = [];
  const liveNotes = memory.notes.filter((note) => !note.retracted);
  const omittedNotes = Math.max(0, liveNotes.length - LIMITS.MAX_NOTES_IN_PROMPT);
  const shownNotes = liveNotes.slice(0, LIMITS.MAX_NOTES_IN_PROMPT);
  if (shownNotes.length > 0) {
    const lines = ["Stored notes:"];
    if (omittedNotes > 0) {
      lines.push(`${omittedNotes} newer notes omitted from this message.`);
    }
    for (const note of shownNotes) {
      lines.push(`${note.id}: ${note.text}`);
    }
    sections.push(lines.join("\n"));
  }

  if (memory.procedures.length > 0) {
    const lines = ["Stored sequences:"];
    for (const procedure of memory.procedures) {
      lines.push(`${procedure.name}: ${visibleKeys(procedure.keys)}`);
    }
    sections.push(lines.join("\n"));
  }

  const omittedEndings = Math.max(0, memory.endings.length - LIMITS.MAX_ENDINGS_IN_PROMPT);
  const shownEndings = memory.endings.slice(omittedEndings);
  if (shownEndings.length > 0) {
    const lines = ["Previous process endings:"];
    if (omittedEndings > 0) {
      lines.push(`${omittedEndings} earlier endings omitted from this message.`);
    }
    for (const ending of shownEndings) {
      lines.push(
        `life ${ending.life}, ${ending.turns} turns, ${ending.exitReason}`,
        excerptScreen(ending.screen),
      );
    }
    sections.push(lines.join("\n"));
  }

  let text = sections.join("\n\n");
  if (text.length > LIMITS.MAX_PROMPT_MEMORY_CHARS) {
    text = `${text.slice(0, LIMITS.MAX_PROMPT_MEMORY_CHARS)}\n(truncated)`;
  }
  return text;
}

function visibleKeys(keys: string): string {
  return JSON.stringify(keys);
}

async function readJson<T>(file: string): Promise<T | undefined> {
  try {
    const raw = await readFile(file, "utf8");
    return JSON.parse(raw) as T;
  } catch {
    return undefined;
  }
}
