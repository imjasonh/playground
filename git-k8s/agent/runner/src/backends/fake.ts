import { readFile, writeFile } from "node:fs/promises";
import { join } from "node:path";
import type { AgentResponse, Backend } from "./types.js";

/** The fake agent fails every added line that holds this. */
export const MARKER = "DO NOT MERGE";

/** A line that the change adds, in the new version of a file. */
export interface AddedLine {
  path: string;
  line: number;
  text: string;
}

/**
 * The fake backend, for tests that run without a Cursor API key. It fails a
 * change that adds a line holding MARKER, and passes any other change. When
 * the task allows edits, it deletes those lines, as a real agent would fix
 * what it found.
 */
export const fakeBackend: Backend = async (request) => {
  const marked = addedLines(request.diff).filter((l) => l.text.includes(MARKER));
  request.log(`fake agent: ${marked.length} added lines hold ${MARKER}`);
  if (request.edit) {
    for (const path of new Set(marked.map((l) => l.path))) {
      const file = join(request.cwd, path);
      const kept = (await readFile(file, "utf8")).split("\n").filter((l) => !l.includes(MARKER));
      await writeFile(file, kept.join("\n"));
    }
  }
  const where = marked.map((l) => `${l.path}:${l.line}`).join(", ");
  const answer =
    marked.length === 0
      ? { verdict: "pass", summary: `no added lines hold ${MARKER}`, reasoning: `The fake agent found no added line that holds ${MARKER}.` }
      : {
          verdict: "fail",
          summary: `${marked.length} added ${marked.length === 1 ? "line holds" : "lines hold"} ${MARKER}`,
          reasoning: `The change adds ${MARKER} at ${where}.${request.edit ? " The fake agent deleted those lines." : ""}`,
        };
  const text = `I read the change.\n\n${JSON.stringify(answer)}\n`;
  const response: AgentResponse = {
    text,
    model: `fake:${request.model}`,
    usage: {
      inputTokens: Math.ceil(request.prompt.length / 4),
      outputTokens: Math.ceil(text.length / 4),
      cacheReadTokens: 0,
      cacheWriteTokens: 0,
    },
  };
  return response;
};

/** Lists the lines that a unified diff adds, with their line numbers. */
export function addedLines(diff: string): AddedLine[] {
  const added: AddedLine[] = [];
  let path: string | undefined;
  let line = 0;
  let inHunk = false;
  for (const text of diff.split("\n")) {
    if (text.startsWith("diff ")) {
      path = undefined;
      inHunk = false;
    } else if (!inHunk && text.startsWith("+++ ")) {
      path = diffPath(text.slice(4));
    } else if (text.startsWith("@@ ")) {
      const m = /^@@ -\d+(?:,\d+)? \+(\d+)/.exec(text);
      line = m ? Number(m[1]) : 0;
      inHunk = true;
    } else if (inHunk && text.startsWith("+") && path !== undefined) {
      added.push({ path, line, text: text.slice(1) });
      line++;
    } else if (inHunk && text.startsWith(" ")) {
      line++;
    }
  }
  return added;
}

function diffPath(field: string): string | undefined {
  let name = field.endsWith("\t") ? field.slice(0, -1) : field;
  if (name === "/dev/null") {
    return undefined;
  }
  if (name.startsWith('"') && name.endsWith('"')) {
    name = name.slice(1, -1).replace(/\\(["\\])/g, "$1");
  }
  return name.startsWith("b/") ? name.slice(2) : name;
}
