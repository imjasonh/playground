#!/usr/bin/env node
import { mkdir, readdir, readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { runGame } from "./harness.js";
import {
  LIMITS,
  assertModelListSize,
  clampGamesPerMatchup,
  clampMaxTurns,
} from "./limits.js";
import {
  DEFAULT_MATRIX_MODELS,
  buildSuiteReport,
  expandMatchups,
  formatSuiteMarkdown,
  gameRecordToRow,
  parseModelList,
  type SuiteGameRow,
} from "./suite-summary.js";
import type { GameRecord } from "./types.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const root = path.resolve(here, "..");

function usage(exitCode = 0): never {
  console.log(`Usage: npm run suite -- <command> [options]

Commands:
  play-matchup     Run N games for one knower×guesser pair
  play-matrix      Run the full model matrix (local / sequential)
  summarize        Aggregate result JSON files into markdown + JSON
  emit-matchups    Print JSON matchup list for GHA matrix (prepare job)

play-matchup options:
  --knower-model <id>
  --guesser-model <id>
  --games <n>              Games for this matchup (default: ${LIMITS.DEFAULT_GAMES_PER_MATCHUP}, max ${LIMITS.MAX_GAMES_PER_MATCHUP})
  --backend mock|cursor    (default: mock)
  --max-turns <n>          (default: ${LIMITS.DEFAULT_MAX_TURNS}, max ${LIMITS.MAX_MAX_TURNS})
  --results-dir <path>     (default: ./results/matrix)
  --verbose

play-matrix options:
  --models <csv>           (default: ${DEFAULT_MATRIX_MODELS.join(",")}; max ${LIMITS.MAX_MODELS})
  --games <n>              Games per matchup (default: ${LIMITS.DEFAULT_GAMES_PER_MATCHUP}, max ${LIMITS.MAX_GAMES_PER_MATCHUP})
  --include-self-play      Include same-model matchups (default: true)
  --no-self-play
  --backend mock|cursor
  --max-turns <n>
  --results-dir <path>
  --verbose

summarize options:
  --results-dir <path>     Directory to scan recursively for *.json records
  --out-dir <path>         Write suite-summary.md + suite-summary.json here
  --games-per-matchup <n>  Label only (default: inferred)

emit-matchups options:
  --models <csv>
  --include-self-play | --no-self-play
`);
  process.exit(exitCode);
}

function argValue(args: string[], name: string): string | undefined {
  const idx = args.indexOf(name);
  if (idx < 0) return undefined;
  return args[idx + 1];
}

function hasFlag(args: string[], name: string): boolean {
  return args.includes(name);
}

async function main(): Promise<void> {
  const args = process.argv.slice(2);
  if (args.length === 0 || hasFlag(args, "--help") || hasFlag(args, "-h")) {
    usage(args.length === 0 ? 1 : 0);
  }

  const command = args[0];
  const rest = args.slice(1);

  if (command === "play-matchup") {
    await playMatchup(rest);
    return;
  }
  if (command === "play-matrix") {
    await playMatrix(rest);
    return;
  }
  if (command === "summarize") {
    await summarize(rest);
    return;
  }
  if (command === "emit-matchups") {
    await emitMatchups(rest);
    return;
  }

  console.error(`Unknown command: ${command}`);
  usage(1);
}

async function playMatchup(args: string[]): Promise<void> {
  const backend = (argValue(args, "--backend") ?? "mock") as "mock" | "cursor";
  const knowerModel = argValue(args, "--knower-model");
  const guesserModel = argValue(args, "--guesser-model");
  if (!knowerModel || !guesserModel) {
    throw new Error("play-matchup requires --knower-model and --guesser-model");
  }
  if (backend === "cursor" && !process.env.CURSOR_API_KEY) {
    throw new Error("CURSOR_API_KEY is required for --backend cursor");
  }

  const games = clampGamesPerMatchup(
    Number(argValue(args, "--games") ?? LIMITS.DEFAULT_GAMES_PER_MATCHUP),
  );
  const maxTurns = clampMaxTurns(
    Number(argValue(args, "--max-turns") ?? LIMITS.DEFAULT_MAX_TURNS),
  );
  const resultsDir = path.resolve(
    root,
    argValue(args, "--results-dir") ?? "results/matrix",
  );
  const matchupDir = path.join(
    resultsDir,
    slug(`${knowerModel}__vs__${guesserModel}`),
  );
  await mkdir(matchupDir, { recursive: true });

  const verbose = hasFlag(args, "--verbose");
  const rows: SuiteGameRow[] = [];

  for (let i = 0; i < games; i++) {
    if (verbose) {
      console.error(
        `[${i + 1}/${games}] knower=${knowerModel} guesser=${guesserModel}`,
      );
    }
    try {
      const record = await runGame({
        gameId: "its-not-jaws",
        backend,
        knowerModel,
        guesserModel,
        maxTurns,
        apiKey: process.env.CURSOR_API_KEY,
        workspacesRoot: path.join(root, ".workspaces"),
        resultsDir: matchupDir,
        verbose,
      });
      rows.push(gameRecordToRow(record));
    } catch (err) {
      const message = err instanceof Error ? err.message : String(err);
      console.error(`Game failed: ${message}`);
      const row: SuiteGameRow = {
        id: `error-${Date.now()}-${i}`,
        knowerModel,
        guesserModel,
        outcome: "aborted",
        gameLength: 0,
        usedLeakedClues: false,
        helpfulClueLeaks: 0,
        totalTokens: 0,
        error: message,
      };
      rows.push(row);
      await writeFile(
        path.join(matchupDir, `${row.id}.summary.json`),
        JSON.stringify(row, null, 2),
        "utf8",
      );
    }
  }

  const matchupSummaryPath = path.join(matchupDir, "matchup-summary.json");
  await writeFile(matchupSummaryPath, JSON.stringify({ rows }, null, 2), "utf8");
  console.log(JSON.stringify({ knowerModel, guesserModel, games, rows }, null, 2));
}

async function playMatrix(args: string[]): Promise<void> {
  const models = parseModelList(
    argValue(args, "--models") ?? DEFAULT_MATRIX_MODELS.join(","),
  );
  assertModelListSize(models);

  const includeSelfPlay = !hasFlag(args, "--no-self-play");
  const matchups = expandMatchups(models, { includeSelfPlay });
  const games = clampGamesPerMatchup(
    Number(argValue(args, "--games") ?? LIMITS.DEFAULT_GAMES_PER_MATCHUP),
  );
  const resultsDir = path.resolve(
    root,
    argValue(args, "--results-dir") ?? "results/matrix",
  );

  console.error(
    `Playing ${matchups.length} matchups × ${games} games (${models.length} models)`,
  );

  for (const m of matchups) {
    await playMatchup([
      "--knower-model",
      m.knower,
      "--guesser-model",
      m.guesser,
      "--games",
      String(games),
      "--backend",
      argValue(args, "--backend") ?? "mock",
      "--max-turns",
      argValue(args, "--max-turns") ?? "8",
      "--results-dir",
      resultsDir,
      ...(hasFlag(args, "--verbose") ? ["--verbose"] : []),
    ]);
  }

  await summarize([
    "--results-dir",
    resultsDir,
    "--out-dir",
    resultsDir,
    "--games-per-matchup",
    String(games),
  ]);
}

async function summarize(args: string[]): Promise<void> {
  const resultsDir = path.resolve(
    root,
    argValue(args, "--results-dir") ?? "results/matrix",
  );
  const outDir = path.resolve(
    root,
    argValue(args, "--out-dir") ?? resultsDir,
  );
  const gamesPerMatchup = Number(argValue(args, "--games-per-matchup") ?? NaN);

  const rows = await collectRows(resultsDir);
  const report = buildSuiteReport(rows, {
    gamesPerMatchup: Number.isFinite(gamesPerMatchup)
      ? gamesPerMatchup
      : undefined,
  });
  const md = formatSuiteMarkdown(report);

  await mkdir(outDir, { recursive: true });
  const mdPath = path.join(outDir, "suite-summary.md");
  const jsonPath = path.join(outDir, "suite-summary.json");
  await writeFile(mdPath, md, "utf8");
  await writeFile(jsonPath, JSON.stringify(report, null, 2), "utf8");

  process.stdout.write(md);
  console.error(`Wrote ${mdPath}`);
  console.error(`Wrote ${jsonPath}`);
}

async function emitMatchups(args: string[]): Promise<void> {
  const models = parseModelList(
    argValue(args, "--models") ?? DEFAULT_MATRIX_MODELS.join(","),
  );
  assertModelListSize(models);
  const includeSelfPlay = !hasFlag(args, "--no-self-play");
  const matchups = expandMatchups(models, { includeSelfPlay }).map((m) => ({
    knower: m.knower,
    guesser: m.guesser,
    name: slug(`${m.knower}__vs__${m.guesser}`),
  }));
  const payload = JSON.stringify(matchups);
  if (hasFlag(args, "--github-output")) {
    const out = process.env.GITHUB_OUTPUT;
    if (!out) throw new Error("GITHUB_OUTPUT is not set");
    // Heredoc so the JSON (commas, quotes) is a valid Actions output value.
    const chunk = [
      `matchups<<EOF_MATCHUPS`,
      payload,
      `EOF_MATCHUPS`,
      `count=${matchups.length}`,
      `models<<EOF_MODELS`,
      JSON.stringify(models),
      `EOF_MODELS`,
      "",
    ].join("\n");
    await writeFile(out, chunk, { encoding: "utf8", flag: "a" });
    console.error(`Emitted ${matchups.length} matchups for ${models.length} models`);
  } else {
    console.log(payload);
  }
}

async function collectRows(dir: string): Promise<SuiteGameRow[]> {
  const files = await walkFiles(dir);
  const rows: SuiteGameRow[] = [];
  const seen = new Set<string>();

  for (const file of files) {
    if (!file.endsWith(".json")) continue;
    const base = path.basename(file);
    if (base === "suite-summary.json" || base === "ci-summary.json") continue;

    let parsed: unknown;
    try {
      parsed = JSON.parse(await readFile(file, "utf8"));
    } catch {
      continue;
    }

    if (isMatchupSummary(parsed)) {
      for (const row of parsed.rows) {
        if (row?.id && !seen.has(row.id)) {
          seen.add(row.id);
          rows.push(row);
        }
      }
      continue;
    }

    if (isGameRecord(parsed)) {
      if (!seen.has(parsed.id)) {
        seen.add(parsed.id);
        rows.push(gameRecordToRow(parsed));
      }
      continue;
    }

    if (isSuiteGameRow(parsed)) {
      if (!seen.has(parsed.id)) {
        seen.add(parsed.id);
        rows.push(parsed);
      }
    }
  }

  return rows;
}

async function walkFiles(dir: string): Promise<string[]> {
  const out: string[] = [];
  let entries;
  try {
    entries = await readdir(dir, { withFileTypes: true });
  } catch {
    return out;
  }
  for (const ent of entries) {
    const full = path.join(dir, ent.name);
    if (ent.isDirectory()) {
      out.push(...(await walkFiles(full)));
    } else if (ent.isFile()) {
      out.push(full);
    }
  }
  return out;
}

function isGameRecord(value: unknown): value is GameRecord {
  if (!value || typeof value !== "object") return false;
  const v = value as Record<string, unknown>;
  return (
    typeof v.id === "string" &&
    typeof v.outcome === "object" &&
    v.outcome !== null &&
    typeof (v.outcome as { kind?: unknown }).kind === "string" &&
    Array.isArray(v.turns)
  );
}

function isMatchupSummary(
  value: unknown,
): value is { rows: SuiteGameRow[] } {
  if (!value || typeof value !== "object") return false;
  const v = value as { rows?: unknown };
  return Array.isArray(v.rows) && v.rows.every(isSuiteGameRow);
}

function isSuiteGameRow(value: unknown): value is SuiteGameRow {
  if (!value || typeof value !== "object") return false;
  const v = value as Record<string, unknown>;
  return (
    typeof v.id === "string" &&
    typeof v.knowerModel === "string" &&
    typeof v.guesserModel === "string" &&
    typeof v.outcome === "string"
  );
}

function slug(s: string): string {
  return s.replace(/[^a-zA-Z0-9._-]+/g, "_").replace(/^_|_$/g, "");
}

main().catch((err) => {
  console.error(err instanceof Error ? err.message : err);
  process.exit(1);
});
