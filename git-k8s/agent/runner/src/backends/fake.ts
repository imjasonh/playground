import { readdir, readFile, writeFile } from "node:fs/promises";
import { join } from "node:path";
import type { AgentResponse, Backend } from "./types.js";

/** The fake agent fails every added line that holds this. */
export const MARKER = "DO NOT MERGE";

/**
 * When the task allows edits, the fake agent replaces each line of the head's
 * files that holds this with the line's indentation and the text after it.
 */
export const FIX_MARKER = "FAKE AGENT FIX:";

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
 * what it found, and applies the fixes that FIX_MARKER lines name, as a real
 * agent would fix code that the change broke.
 */
export const fakeBackend: Backend = async (request) => {
  const marked = addedLines(request.diff).filter((l) => l.text.includes(MARKER));
  request.log(`fake agent: ${marked.length} added lines hold ${MARKER}`);
  let fixed = 0;
  if (request.edit) {
    for (const path of new Set(marked.map((l) => l.path))) {
      const file = join(request.cwd, path);
      const kept = (await readFile(file, "utf8")).split("\n").filter((l) => !l.includes(MARKER));
      await writeFile(file, kept.join("\n"));
    }
    fixed = await applyFixes(request.cwd);
    request.log(`fake agent: applied ${fixed} fixes`);
  }
  const where = marked.map((l) => `${l.path}:${l.line}`).join(", ");
  const answer =
    marked.length > 0
      ? {
          verdict: "fail",
          summary: `${marked.length} added ${marked.length === 1 ? "line holds" : "lines hold"} ${MARKER}`,
          reasoning: `The change adds ${MARKER} at ${where}.${request.edit ? " The fake agent deleted those lines." : ""}`,
        }
      : fixed > 0
        ? {
            verdict: "pass",
            summary: `applied ${fixed} ${fixed === 1 ? "fix" : "fixes"}`,
            reasoning: `The fake agent replaced ${fixed} ${fixed === 1 ? "line that holds" : "lines that hold"} ${FIX_MARKER} with the text after it.`,
          }
        : { verdict: "pass", summary: `no added lines hold ${MARKER}`, reasoning: `The fake agent found no added line that holds ${MARKER}.` };
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

/**
 * Replaces each line in the files under dir that holds FIX_MARKER, and
 * returns how many lines it replaced. It skips symbolic links.
 */
async function applyFixes(dir: string): Promise<number> {
  let fixed = 0;
  for (const entry of await readdir(dir, { withFileTypes: true })) {
    const file = join(dir, entry.name);
    if (entry.isDirectory()) {
      fixed += await applyFixes(file);
      continue;
    }
    const data = entry.isFile() ? await readFile(file) : undefined;
    if (!data?.includes(FIX_MARKER)) {
      continue;
    }
    const lines = data.toString("utf8").split("\n");
    for (const [i, line] of lines.entries()) {
      const at = line.indexOf(FIX_MARKER);
      if (at >= 0) {
        lines[i] = (/^\s*/.exec(line)?.[0] ?? "") + line.slice(at + FIX_MARKER.length).trim();
        fixed++;
      }
    }
    await writeFile(file, lines.join("\n"));
  }
  return fixed;
}

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
