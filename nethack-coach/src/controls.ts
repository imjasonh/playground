import { rm, stat } from "node:fs/promises";
import path from "node:path";
import type { Controls } from "./types.js";

/**
 * Read the on-demand hotkeys. The tmux bindings drop marker files into the
 * control directory; each poll consumes whatever is there.
 */
export function makeFileControls(controlDir: string): () => Promise<Controls> {
  return async () => ({
    ask: await consume(path.join(controlDir, "ask")),
    toggle: await consume(path.join(controlDir, "toggle")),
  });
}

async function consume(file: string): Promise<boolean> {
  try {
    await stat(file);
  } catch {
    return false;
  }
  await rm(file, { force: true });
  return true;
}
