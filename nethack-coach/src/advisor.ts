#!/usr/bin/env node
import path from "node:path";
import { fileURLToPath } from "node:url";
import { makeFileControls } from "./controls.js";
import { createCursorAdvisor } from "./cursor.js";
import { paintSidebar } from "./render.js";
import { makeTmuxCapture } from "./screen.js";
import { runLoop } from "./loop.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const root = path.resolve(here, "..");

function argValue(args: string[], name: string): string | undefined {
  const idx = args.indexOf(name);
  return idx < 0 ? undefined : args[idx + 1];
}

async function main(): Promise<void> {
  const args = process.argv.slice(2);
  const socket = argValue(args, "--socket") ?? "nethack-coach";
  const gamePane = argValue(args, "--game-pane");
  const controlDir = argValue(args, "--control-dir");
  const model = argValue(args, "--model") ?? "grok-4.6";
  const sidebarCols = Number(argValue(args, "--sidebar-cols") ?? process.stdout.columns ?? 46);

  if (!gamePane) throw new Error("--game-pane is required");
  if (!controlDir) throw new Error("--control-dir is required");
  if (!process.env.CURSOR_API_KEY) throw new Error("CURSOR_API_KEY is required");

  const width = () => process.stdout.columns ?? sidebarCols;
  const advisor = await createCursorAdvisor({
    model,
    sidebarCols,
    workspaceDir: path.join(root, ".workspace"),
    apiKey: process.env.CURSOR_API_KEY,
  });

  const summary = await runLoop(
    {
      capture: makeTmuxCapture(socket, gamePane),
      controls: makeFileControls(controlDir),
      advisor,
      paint: (view) => paintSidebar(view, width(), (s) => process.stdout.write(s)),
      now: () => Date.now(),
      sleep: (ms) => new Promise((resolve) => setTimeout(resolve, ms)),
    },
    { settleMs: 700, cooldownMs: 6_000, pollMs: 400 },
  );

  await advisor.dispose();
  process.stdout.write(
    `\r\n\r\nSession ended. ${summary.adviceCount} tips, ${summary.usage.totalTokens.toLocaleString("en-US")} tokens.\r\n`,
  );
}

main().catch((err) => {
  process.stderr.write(`${err instanceof Error ? err.message : String(err)}\n`);
  process.exit(1);
});
