#!/usr/bin/env node
import { existsSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { runSession } from "./harness.js";
import { LIMITS, clampLives, clampMaxTurns } from "./limits.js";
import { assertLearningGame, defaultNethackCommand } from "./real-game.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const root = path.resolve(here, "..");
const notebookDir = path.join(root, "notebook");

function usage(): never {
  console.log(`Usage: npm run play -- [options]

Options:
  --backend cursor        Learning agent (required)
  --model <id>            Model id (default: ${LIMITS.DEFAULT_MODEL})
  --lives <n>             Lives in this run (default: ${LIMITS.DEFAULT_LIVES}, max ${LIMITS.MAX_LIVES})
  --max-turns <n>         Model turns per life (default: ${LIMITS.DEFAULT_MAX_TURNS}, max ${LIMITS.MAX_MAX_TURNS})
  --command <bin>         nethack binary (default: ${defaultNethackCommand()})
  --results-dir <path>    Per-run transcripts (default: ./results)
  --verbose               Log life outcomes on stderr
  --help                  Show help

Play always runs the nethack process and resumes notebook/.
The fake screen is not available here. Tests use it without writing notes.
`);
  process.exit(0);
}

function argValue(args: string[], name: string): string | undefined {
  const idx = args.indexOf(name);
  if (idx < 0) return undefined;
  return args[idx + 1];
}

async function main(): Promise<void> {
  const args = process.argv.slice(2);
  if (args.includes("--help") || args.includes("-h")) usage();

  const backend = argValue(args, "--backend") ?? "cursor";
  if (backend !== "cursor") {
    throw new Error(
      "play only runs the cursor agent against nethack. The fake screen is for tests.",
    );
  }
  const game = argValue(args, "--game") ?? "tty";
  assertLearningGame(game);
  if (!process.env.CURSOR_API_KEY) {
    throw new Error("CURSOR_API_KEY is required to play nethack");
  }
  const command = argValue(args, "--command") ?? defaultNethackCommand();
  if (!existsSync(command) && command.includes("/")) {
    throw new Error(`nethack binary not found: ${command}`);
  }

  const record = await runSession({
    backend: "cursor",
    game: "tty",
    model: argValue(args, "--model") ?? LIMITS.DEFAULT_MODEL,
    lives: clampLives(Number(argValue(args, "--lives") ?? LIMITS.DEFAULT_LIVES)),
    maxTurns: clampMaxTurns(
      Number(argValue(args, "--max-turns") ?? LIMITS.DEFAULT_MAX_TURNS),
    ),
    seed: 1,
    apiKey: process.env.CURSOR_API_KEY,
    resultsDir: path.resolve(root, argValue(args, "--results-dir") ?? "results"),
    workspacesRoot: path.join(root, ".workspaces"),
    resumeMemoryDir: notebookDir,
    notebookDir,
    tty: { command },
    verbose: args.includes("--verbose"),
  });

  const last = record.lives[record.lives.length - 1];
  console.log(
    JSON.stringify(
      {
        id: record.id,
        game: record.game,
        command,
        backend: record.backend,
        model: record.model,
        notebook: notebookDir,
        lives: record.lives.map((life) => ({
          life: life.life,
          turns: life.turns,
          exitReason: life.exitReason,
        })),
        notes: record.memory.notes.filter((note) => !note.retracted).length,
        sequences: record.memory.procedures.length,
        lastExit: last?.exitReason,
        totalTokens: record.usage.totalTokens,
        totalRawCostCents: record.usage.totalRawCostCents,
      },
      null,
      2,
    ),
  );
}

main().catch((err) => {
  console.error(err instanceof Error ? err.message : err);
  process.exit(1);
});
