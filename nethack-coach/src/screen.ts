import { spawn } from "node:child_process";
import type { Capture } from "./types.js";

/** Trailing whitespace and blank lines are noise for a terminal screen. */
export function normalizeScreen(screen: string): string {
  const lines = screen.replace(/\r/g, "").split("\n").map((line) => line.replace(/\s+$/u, ""));
  while (lines.length > 1 && lines[lines.length - 1] === "") lines.pop();
  return lines.join("\n");
}

export function screensEqual(a: string, b: string): boolean {
  return normalizeScreen(a) === normalizeScreen(b);
}

/**
 * A line-by-line difference between two screens, as plain text.
 *
 * The model already gets the current screen, so this just points at what moved:
 * `-` lines left, `+` lines arrived. Returns an empty string when nothing changed.
 */
export function diffScreens(previous: string, next: string): string {
  const before = normalizeScreen(previous).split("\n");
  const after = normalizeScreen(next).split("\n");
  const rows = Math.max(before.length, after.length);
  const out: string[] = [];
  for (let i = 0; i < rows; i++) {
    const a = before[i] ?? "";
    const b = after[i] ?? "";
    if (a === b) continue;
    if (a) out.push(`- ${a}`);
    if (b) out.push(`+ ${b}`);
  }
  return out.join("\n");
}

/**
 * Read the game pane through tmux. Returns `ok: false` when the pane no longer
 * exists, which is how the loop learns the session is over.
 */
export function makeTmuxCapture(socket: string, pane: string): () => Promise<Capture> {
  return async () => {
    const screen = await runTmux(socket, ["capture-pane", "-p", "-t", pane]);
    if (screen === null) return { ok: false };
    const deadFlag = await runTmux(socket, [
      "display-message",
      "-p",
      "-t",
      pane,
      "#{pane_dead}",
    ]);
    return { ok: true, screen, dead: deadFlag?.trim() === "1" };
  };
}

function runTmux(socket: string, args: string[]): Promise<string | null> {
  return new Promise((resolve) => {
    const child = spawn("tmux", ["-L", socket, ...args], {
      stdio: ["ignore", "pipe", "ignore"],
    });
    let out = "";
    child.stdout.on("data", (chunk: Buffer) => {
      out += chunk.toString("utf8");
    });
    child.on("error", () => resolve(null));
    child.on("close", (code) => resolve(code === 0 ? out : null));
  });
}
