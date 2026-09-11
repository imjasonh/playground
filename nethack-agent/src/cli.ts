#!/usr/bin/env node
import path from "node:path";
import { fileURLToPath } from "node:url";
import { runSession } from "./harness.js";
import { LIMITS, clampLives, clampMaxTurns } from "./limits.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const root = path.resolve(here, "..");

function usage(): never {
  console.log(`Usage: npm run play -- [options]

Options:
  --backend mock|cursor   Agent backend (default: mock)
  --game fake|tty         Screen source (default: fake)
  --model <id>            Model id (default: ${LIMITS.DEFAULT_MODEL})
  --lives <n>             Lives in this run (default: ${LIMITS.DEFAULT_LIVES}, max ${LIMITS.MAX_LIVES})
  --max-turns <n>         Model turns per life (default: ${LIMITS.DEFAULT_MAX_TURNS}, max ${LIMITS.MAX_MAX_TURNS})
  --seed <n>              Fake-game layout seed (default: 1)
  --command <bin>         tty game binary (default: nethack)
  --resume <dir>          Load notes from a previous run's memory directory
  --results-dir <path>    Where to write records (default: ./results)
  --verbose               Log life outcomes on stderr
  --help                  Show help

The agent prompt does not name the game or list commands. See DESIGN.md.
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

  const backend = (argValue(args, "--backend") ?? "mock") as "mock" | "cursor";
  if (backend !== "mock" && backend !== "cursor") {
    throw new Error(`Invalid --backend: ${backend}`);
  }
  const game = (argValue(args, "--game") ?? "fake") as "fake" | "tty";
  if (game !== "fake" && game !== "tty") {
    throw new Error(`Invalid --game: ${game}`);
  }
  if (backend === "cursor" && !process.env.CURSOR_API_KEY) {
    throw new Error("CURSOR_API_KEY is required for --backend cursor");
  }

  const record = await runSession({
    backend,
    game,
    model: argValue(args, "--model") ?? LIMITS.DEFAULT_MODEL,
    lives: clampLives(Number(argValue(args, "--lives") ?? LIMITS.DEFAULT_LIVES)),
    maxTurns: clampMaxTurns(
      Number(argValue(args, "--max-turns") ?? LIMITS.DEFAULT_MAX_TURNS),
    ),
    seed: Number(argValue(args, "--seed") ?? 1),
    apiKey: process.env.CURSOR_API_KEY,
    resultsDir: path.resolve(root, argValue(args, "--results-dir") ?? "results"),
    workspacesRoot: path.join(root, ".workspaces"),
    resumeMemoryDir: argValue(args, "--resume"),
    tty: { command: argValue(args, "--command") ?? "nethack" },
    verbose: args.includes("--verbose"),
  });

  const last = record.lives[record.lives.length - 1];
  console.log(
    JSON.stringify(
      {
        id: record.id,
        game: record.game,
        backend: record.backend,
        model: record.model,
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
