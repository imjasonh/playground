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
  --game <id>             Game definition (default: stub-noun)
  --keeper-model <id>     Keeper model id (default: composer-2.5)
  --guesser-model <id>    Guesser model id (default: composer-2.5)
  --max-turns <n>         Max guesser turns (default: 8)
  --seed <n>              Deterministic secret pick (and mock behavior)
  --secret <text>         Override harness-assigned secret
  --results-dir <path>    Where to write JSON records (default: ./results)
  --verbose               Log paths / progress
  --help                  Show help

Examples:
  npm run play:mock
  npm run play -- --backend cursor --keeper-model composer-2.5 --guesser-model gpt-5.5
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

  const maxTurns = Number(argValue(args, "--max-turns") ?? 8);
  const seedRaw = argValue(args, "--seed");
  const seed =
    seedRaw == null ? undefined : Number(seedRaw);
  if (seedRaw != null && !Number.isFinite(seed)) {
    throw new Error(`Invalid --seed: ${seedRaw}`);
  }

  const record = await runGame({
    gameId: argValue(args, "--game") ?? "stub-noun",
    backend,
    keeperModel: argValue(args, "--keeper-model") ?? "composer-2.5",
    guesserModel: argValue(args, "--guesser-model") ?? "composer-2.5",
    maxTurns: Number.isFinite(maxTurns) ? maxTurns : 8,
    seed,
    secret: argValue(args, "--secret"),
    apiKey: process.env.CURSOR_API_KEY,
    workspacesRoot: path.join(root, ".workspaces"),
    resultsDir: path.resolve(
      root,
      argValue(args, "--results-dir") ?? "results",
    ),
    verbose: args.includes("--verbose"),
  });

  const summary = {
    id: record.id,
    outcome: record.outcome,
    secret: record.secret,
    gameLength: record.gameLength,
    totalTokens: record.usage.totalTokens,
    totalRawCostCents: record.usage.totalRawCostCents,
    keeperModel: record.keeperModel,
    guesserModel: record.guesserModel,
  };
  console.log(JSON.stringify(summary, null, 2));
}

main().catch((err) => {
  console.error(err instanceof Error ? err.message : err);
  process.exit(1);
});
