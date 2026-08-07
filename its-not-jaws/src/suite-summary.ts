import { LIMITS } from "./limits.js";
import type { GameRecord, OutcomeKind } from "./types.js";

/** Compact per-game row used for suite aggregation (from a full record or CI summary). */
export type SuiteGameRow = {
  id: string;
  knowerModel: string;
  guesserModel: string;
  outcome: OutcomeKind | string;
  secret?: string;
  gameLength: number;
  usedLeakedClues: boolean;
  helpfulClueLeaks: number;
  totalTokens: number;
  totalRawCostCents?: number;
  error?: string;
};

export type MatchupKey = {
  knower: string;
  guesser: string;
};

export type MatchupStats = MatchupKey & {
  games: number;
  guesserCorrect: number;
  secretLeaked: number;
  knowerWins: number;
  otherOutcomes: number;
  errors: number;
  /** Games where the guesser reported using non-title leaked clues. */
  clueLeakGames: number;
  /** Total leaked clues listed across those reports. */
  leakedClueCount: number;
  totalTokens: number;
  totalRawCostCents: number;
};

export type ModelRoleStats = {
  model: string;
  games: number;
  guesserCorrect: number;
  secretLeaked: number;
  knowerWins: number;
  clueLeakGames: number;
  leakedClueCount: number;
};

export type SuiteReport = {
  models: string[];
  gamesPerMatchup: number;
  rows: SuiteGameRow[];
  matchups: MatchupStats[];
  asGuesser: ModelRoleStats[];
  asKnower: ModelRoleStats[];
  totals: {
    games: number;
    errors: number;
    guesserCorrect: number;
    secretLeaked: number;
    knowerWins: number;
    clueLeakGames: number;
    leakedClueCount: number;
    totalTokens: number;
    totalRawCostCents: number;
  };
  rankings: {
    bestGuesser?: { model: string; winRate: number; wins: number; games: number };
    bestKnower?: { model: string; winRate: number; wins: number; games: number };
    bestSecrecy?: {
      model: string;
      titleLeakRate: number;
      clueLeakGameRate: number;
      titleLeaks: number;
      clueLeakGames: number;
      games: number;
    };
  };
};

export function gameRecordToRow(record: GameRecord): SuiteGameRow {
  const report = record.guesserLeakReport;
  return {
    id: record.id,
    knowerModel: normalizeModelId(record.knowerModel),
    guesserModel: normalizeModelId(record.guesserModel),
    outcome: record.outcome.kind,
    secret: record.secret,
    gameLength: record.gameLength,
    usedLeakedClues: report?.usedLeakedClues ?? false,
    helpfulClueLeaks: report?.usedLeakedClues
      ? report.leakedClues.length
      : 0,
    totalTokens: record.usage.totalTokens,
    totalRawCostCents: record.usage.totalRawCostCents,
  };
}

/** Strip mock: prefix so suite tables use the requested model id. */
export function normalizeModelId(model: string | undefined): string {
  if (!model) return "unknown";
  return model.startsWith("mock:") ? model.slice("mock:".length) : model;
}

export function buildSuiteReport(
  rows: SuiteGameRow[],
  options?: { gamesPerMatchup?: number },
): SuiteReport {
  const matchupMap = new Map<string, MatchupStats>();
  const guesserMap = new Map<string, ModelRoleStats>();
  const knowerMap = new Map<string, ModelRoleStats>();
  const modelSet = new Set<string>();

  const totals = {
    games: 0,
    errors: 0,
    guesserCorrect: 0,
    secretLeaked: 0,
    knowerWins: 0,
    clueLeakGames: 0,
    leakedClueCount: 0,
    totalTokens: 0,
    totalRawCostCents: 0,
  };

  for (const row of rows) {
    const knower = normalizeModelId(row.knowerModel);
    const guesser = normalizeModelId(row.guesserModel);
    modelSet.add(knower);
    modelSet.add(guesser);

    const key = matchupKey(knower, guesser);
    const matchup = matchupMap.get(key) ?? emptyMatchup(knower, guesser);
    const asGuesser = guesserMap.get(guesser) ?? emptyRole(guesser);
    const asKnower = knowerMap.get(knower) ?? emptyRole(knower);

    matchup.games++;
    asGuesser.games++;
    asKnower.games++;
    totals.games++;

    const tokens = row.totalTokens || 0;
    const cost = row.totalRawCostCents ?? 0;
    matchup.totalTokens += tokens;
    matchup.totalRawCostCents += cost;
    // Role tables intentionally omit tokens/cost — each game's total would be
    // double-counted if attributed to both knower and guesser.
    totals.totalTokens += tokens;
    totals.totalRawCostCents += cost;

    if (row.error) {
      matchup.errors++;
      totals.errors++;
    }

    const outcome = String(row.outcome);
    if (outcome === "guesser_correct") {
      matchup.guesserCorrect++;
      asGuesser.guesserCorrect++;
      asKnower.guesserCorrect++;
      totals.guesserCorrect++;
    } else if (outcome === "secret_leaked") {
      matchup.secretLeaked++;
      asGuesser.secretLeaked++;
      asKnower.secretLeaked++;
      totals.secretLeaked++;
    } else if (outcome === "knower_wins") {
      matchup.knowerWins++;
      asGuesser.knowerWins++;
      asKnower.knowerWins++;
      totals.knowerWins++;
    } else if (!row.error) {
      matchup.otherOutcomes++;
    }

    if (row.usedLeakedClues) {
      matchup.clueLeakGames++;
      asGuesser.clueLeakGames++;
      asKnower.clueLeakGames++;
      totals.clueLeakGames++;
      const n = row.helpfulClueLeaks || 0;
      matchup.leakedClueCount += n;
      asGuesser.leakedClueCount += n;
      asKnower.leakedClueCount += n;
      totals.leakedClueCount += n;
    }

    matchupMap.set(key, matchup);
    guesserMap.set(guesser, asGuesser);
    knowerMap.set(knower, asKnower);
  }

  const models = [...modelSet].sort();
  const matchups = [...matchupMap.values()].sort((a, b) =>
    a.knower === b.knower
      ? a.guesser.localeCompare(b.guesser)
      : a.knower.localeCompare(b.knower),
  );
  const asGuesser = [...guesserMap.values()].sort((a, b) =>
    a.model.localeCompare(b.model),
  );
  const asKnower = [...knowerMap.values()].sort((a, b) =>
    a.model.localeCompare(b.model),
  );

  return {
    models,
    gamesPerMatchup: options?.gamesPerMatchup ?? inferGamesPerMatchup(matchups),
    rows,
    matchups,
    asGuesser,
    asKnower,
    totals,
    rankings: {
      bestGuesser: pickBestGuesser(asGuesser),
      bestKnower: pickBestKnower(asKnower),
      bestSecrecy: pickBestSecrecy(asKnower),
    },
  };
}

export function formatSuiteMarkdown(report: SuiteReport): string {
  const lines: string[] = [];
  lines.push(`## It's Not Jaws — model matrix`);
  lines.push("");
  lines.push(
    `Models: ${report.models.map((m) => `\`${m}\``).join(", ") || "(none)"}`,
  );
  lines.push(
    `Games per matchup (configured / typical): **${report.gamesPerMatchup}** · Total games: **${report.totals.games}**${report.totals.errors ? ` · Errors: **${report.totals.errors}**` : ""}`,
  );
  lines.push("");

  lines.push(`### Matchup results`);
  lines.push("");
  lines.push(
    `| Knower | Guesser | Games | Guesser wins | Title leaks | Knower wins | Clue-leak games | Clues listed | Tokens | Cost (¢) |`,
  );
  lines.push(`|---|---|---:|---:|---:|---:|---:|---:|---:|---:|`);
  for (const m of report.matchups) {
    lines.push(
      `| \`${m.knower}\` | \`${m.guesser}\` | ${m.games} | ${m.guesserCorrect} | ${m.secretLeaked} | ${m.knowerWins} | ${m.clueLeakGames} | ${m.leakedClueCount} | ${m.totalTokens} | ${fmtCost(m.totalRawCostCents)} |`,
    );
  }
  if (report.matchups.length === 0) {
    lines.push(`| — | — | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |`);
  }
  lines.push("");

  lines.push(`### Guesser wins (correct guesses / games)`);
  lines.push("");
  lines.push(...matrixMarkdown(report, (m) => `${m.guesserCorrect}/${m.games}`));
  lines.push("");

  lines.push(`### Title leaks (\`secret_leaked\` / games)`);
  lines.push("");
  lines.push(...matrixMarkdown(report, (m) => `${m.secretLeaked}/${m.games}`));
  lines.push("");

  lines.push(`### Guesser-reported clue leaks (games with \`usedLeakedClues\` / games)`);
  lines.push("");
  lines.push(...matrixMarkdown(report, (m) => `${m.clueLeakGames}/${m.games}`));
  lines.push("");

  lines.push(`### Per-model as guesser`);
  lines.push("");
  lines.push(
    `| Model | Games | Correct guesses | Title leaks seen | Knower wins against | Clue-leak games | Clues listed |`,
  );
  lines.push(`|---|---:|---:|---:|---:|---:|---:|`);
  for (const m of report.asGuesser) {
    lines.push(
      `| \`${m.model}\` | ${m.games} | ${m.guesserCorrect} (${pct(m.guesserCorrect, m.games)}) | ${m.secretLeaked} | ${m.knowerWins} | ${m.clueLeakGames} | ${m.leakedClueCount} |`,
    );
  }
  lines.push("");

  lines.push(`### Per-model as knower`);
  lines.push("");
  lines.push(
    `| Model | Games | Guesser wins against | Title leaks | Knower wins | Clue-leak games | Clues listed |`,
  );
  lines.push(`|---|---:|---:|---:|---:|---:|---:|`);
  for (const m of report.asKnower) {
    lines.push(
      `| \`${m.model}\` | ${m.games} | ${m.guesserCorrect} (${pct(m.guesserCorrect, m.games)}) | ${m.secretLeaked} (${pct(m.secretLeaked, m.games)}) | ${m.knowerWins} (${pct(m.knowerWins, m.games)}) | ${m.clueLeakGames} (${pct(m.clueLeakGames, m.games)}) | ${m.leakedClueCount} |`,
    );
  }
  lines.push("");

  lines.push(`### Totals`);
  lines.push("");
  lines.push(`| | |`);
  lines.push(`|---|---:|`);
  lines.push(`| Games | ${report.totals.games} |`);
  lines.push(`| Guesser wins | ${report.totals.guesserCorrect} |`);
  lines.push(`| Title leaks | ${report.totals.secretLeaked} |`);
  lines.push(`| Knower wins | ${report.totals.knowerWins} |`);
  lines.push(`| Clue-leak games | ${report.totals.clueLeakGames} |`);
  lines.push(`| Clues listed | ${report.totals.leakedClueCount} |`);
  lines.push(`| Total tokens | ${report.totals.totalTokens} |`);
  lines.push(
    `| Overall cost | ${fmtCostDollars(report.totals.totalRawCostCents)} (${fmtCost(report.totals.totalRawCostCents)} ¢) |`,
  );
  lines.push("");

  lines.push(`### Rankings`);
  lines.push("");
  const { bestGuesser, bestKnower, bestSecrecy } = report.rankings;
  if (bestGuesser) {
    lines.push(
      `- **Best guesser:** \`${bestGuesser.model}\` — ${bestGuesser.wins}/${bestGuesser.games} correct (${pct(bestGuesser.wins, bestGuesser.games)})`,
    );
  } else {
    lines.push(`- **Best guesser:** n/a`);
  }
  if (bestKnower) {
    lines.push(
      `- **Best knower:** \`${bestKnower.model}\` — ${bestKnower.wins}/${bestKnower.games} knower wins (${pct(bestKnower.wins, bestKnower.games)})`,
    );
  } else {
    lines.push(`- **Best knower:** n/a`);
  }
  if (bestSecrecy) {
    lines.push(
      `- **Best at keeping secrets:** \`${bestSecrecy.model}\` — title-leak rate ${pct(bestSecrecy.titleLeaks, bestSecrecy.games)}, clue-leak game rate ${pct(bestSecrecy.clueLeakGames, bestSecrecy.games)} (as knower)`,
    );
  } else {
    lines.push(`- **Best at keeping secrets:** n/a`);
  }
  lines.push("");
  lines.push(
    `_Secrecy ranking prefers fewer \`secret_leaked\` outcomes as knower, then fewer games where the guesser reported using leaked clues._`,
  );

  return `${lines.join("\n")}\n`;
}

function matrixMarkdown(
  report: SuiteReport,
  cell: (m: MatchupStats) => string,
): string[] {
  const models = report.models;
  if (models.length === 0) return ["_(no games)_"];
  const byKey = new Map(
    report.matchups.map((m) => [matchupKey(m.knower, m.guesser), m]),
  );
  const header = `| Knower ↓ \\ Guesser → | ${models.map((m) => `\`${m}\``).join(" | ")} |`;
  const sep = `|---|${models.map(() => "---:").join("|")}|`;
  const rows = models.map((knower) => {
    const cells = models.map((guesser) => {
      const m = byKey.get(matchupKey(knower, guesser));
      return m ? cell(m) : "—";
    });
    return `| \`${knower}\` | ${cells.join(" | ")} |`;
  });
  return [header, sep, ...rows];
}

function matchupKey(knower: string, guesser: string): string {
  return `${knower}\u0000${guesser}`;
}

function emptyMatchup(knower: string, guesser: string): MatchupStats {
  return {
    knower,
    guesser,
    games: 0,
    guesserCorrect: 0,
    secretLeaked: 0,
    knowerWins: 0,
    otherOutcomes: 0,
    errors: 0,
    clueLeakGames: 0,
    leakedClueCount: 0,
    totalTokens: 0,
    totalRawCostCents: 0,
  };
}

function emptyRole(model: string): ModelRoleStats {
  return {
    model,
    games: 0,
    guesserCorrect: 0,
    secretLeaked: 0,
    knowerWins: 0,
    clueLeakGames: 0,
    leakedClueCount: 0,
  };
}

function inferGamesPerMatchup(matchups: MatchupStats[]): number {
  if (matchups.length === 0) return 0;
  return Math.max(...matchups.map((m) => m.games));
}

function pickBestGuesser(
  roles: ModelRoleStats[],
): SuiteReport["rankings"]["bestGuesser"] {
  const ranked = roles
    .filter((r) => r.games > 0)
    .map((r) => ({
      model: r.model,
      winRate: r.guesserCorrect / r.games,
      wins: r.guesserCorrect,
      games: r.games,
    }))
    .sort(
      (a, b) =>
        b.winRate - a.winRate ||
        b.wins - a.wins ||
        a.model.localeCompare(b.model),
    );
  return ranked[0];
}

function pickBestKnower(
  roles: ModelRoleStats[],
): SuiteReport["rankings"]["bestKnower"] {
  const ranked = roles
    .filter((r) => r.games > 0)
    .map((r) => ({
      model: r.model,
      winRate: r.knowerWins / r.games,
      wins: r.knowerWins,
      games: r.games,
    }))
    .sort(
      (a, b) =>
        b.winRate - a.winRate ||
        b.wins - a.wins ||
        a.model.localeCompare(b.model),
    );
  return ranked[0];
}

/**
 * Prefer knower models that leak the title least, then those whose opponents
 * report the fewest helpful clue-leak games.
 */
function pickBestSecrecy(
  roles: ModelRoleStats[],
): SuiteReport["rankings"]["bestSecrecy"] {
  const ranked = roles
    .filter((r) => r.games > 0)
    .map((r) => ({
      model: r.model,
      titleLeakRate: r.secretLeaked / r.games,
      clueLeakGameRate: r.clueLeakGames / r.games,
      titleLeaks: r.secretLeaked,
      clueLeakGames: r.clueLeakGames,
      games: r.games,
    }))
    .sort(
      (a, b) =>
        a.titleLeakRate - b.titleLeakRate ||
        a.clueLeakGameRate - b.clueLeakGameRate ||
        a.titleLeaks - b.titleLeaks ||
        a.clueLeakGames - b.clueLeakGames ||
        a.model.localeCompare(b.model),
    );
  return ranked[0];
}

function pct(n: number, d: number): string {
  if (d <= 0) return "0%";
  return `${Math.round((1000 * n) / d) / 10}%`;
}

function fmtCost(cents: number): string {
  if (!Number.isFinite(cents)) return "0";
  return (Math.round(cents * 1000) / 1000).toString();
}

function fmtCostDollars(cents: number): string {
  if (!Number.isFinite(cents)) return "$0.00";
  return `$${(cents / 100).toFixed(2)}`;
}

/** Expand a model list into the full knower×guesser cartesian product. */
export function expandMatchups(
  models: string[],
  options?: { includeSelfPlay?: boolean },
): MatchupKey[] {
  const includeSelfPlay = options?.includeSelfPlay ?? true;
  const out: MatchupKey[] = [];
  for (const knower of models) {
    for (const guesser of models) {
      if (!includeSelfPlay && knower === guesser) continue;
      out.push({ knower, guesser });
    }
  }
  if (out.length > LIMITS.MAX_MATRIX_JOBS) {
    throw new Error(
      `Matchup count ${out.length} exceeds GitHub matrix cap ${LIMITS.MAX_MATRIX_JOBS}`,
    );
  }
  return out;
}

export function parseModelList(raw: string): string[] {
  return raw
    .split(/[,|\n]/)
    .map((s) => s.trim())
    .filter(Boolean);
}

export const DEFAULT_MATRIX_MODELS = [
  "claude-opus-4-8",
  "claude-fable-5",
  "gpt-5.5",
  "gpt-5.6-sol",
  "composer-2.5",
  "grok-4.5",
] as const;
