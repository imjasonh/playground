#!/usr/bin/env node
import path from "node:path";
import { fileURLToPath } from "node:url";
import { runGame } from "./harness.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const root = path.resolve(here, "..");

function usage(): never {
  console.log(`Usage: npm run play -- [options]

Options:
  --backend mock|cursor   Agent backend (default: mock)
  --game <id>             Game definition (default: its-not-jaws)
  --knower-model <id>     Knower model id (default: composer-2.5)
  --guesser-model <id>    Guesser model id (default: composer-2.5)
  --max-turns <n>         Max guesser turns (default: 8)
  --results-dir <path>    Where to write JSON records (default: ./results)
  --verbose               Log paths / progress
  --help                  Show help

Examples:
  npm run play:mock
  npm run play -- --backend cursor --knower-model composer-2.5 --guesser-model gpt-5.5
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
  if (backend === "cursor" && !process.env.CURSOR_API_KEY) {
    throw new Error("CURSOR_API_KEY is required for --backend cursor");
  }

  // Back-compat alias from earlier keeper naming.
  const knowerModel =
    argValue(args, "--knower-model") ??
    argValue(args, "--keeper-model") ??
    "composer-2.5";

  const maxTurns = Number(argValue(args, "--max-turns") ?? 8);
  const record = await runGame({
    gameId: argValue(args, "--game") ?? "its-not-jaws",
    backend,
    knowerModel,
    guesserModel: argValue(args, "--guesser-model") ?? "composer-2.5",
    maxTurns: Number.isFinite(maxTurns) ? maxTurns : 8,
    apiKey: process.env.CURSOR_API_KEY,
    workspacesRoot: path.join(root, ".workspaces"),
    resultsDir: path.resolve(
      root,
      argValue(args, "--results-dir") ?? "results",
    ),
    verbose: args.includes("--verbose"),
  });

  const helpfulClueLeaks = record.clueLeaks.filter(
    (l) => l.helpful && !l.isTitleLeak,
  );
  const summary = {
    id: record.id,
    outcome: record.outcome,
    secret: record.secret,
    gameLength: record.gameLength,
    helpfulClueLeaks: helpfulClueLeaks.length,
    clueLeaks: record.clueLeaks,
    totalTokens: record.usage.totalTokens,
    totalRawCostCents: record.usage.totalRawCostCents,
    knowerModel: record.knowerModel,
    guesserModel: record.guesserModel,
  };
  console.log(JSON.stringify(summary, null, 2));
}

main().catch((err) => {
  console.error(err instanceof Error ? err.message : err);
  process.exit(1);
});
