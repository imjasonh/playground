import assert from "node:assert/strict";
import { describe, it } from "node:test";
import {
  DEFAULT_MATRIX_MODELS,
  buildSuiteReport,
  expandMatchups,
  formatSuiteMarkdown,
  parseModelList,
  type SuiteGameRow,
} from "../src/suite-summary.js";

function row(
  partial: Partial<SuiteGameRow> &
    Pick<SuiteGameRow, "id" | "knowerModel" | "guesserModel" | "outcome">,
): SuiteGameRow {
  return {
    gameLength: 3,
    usedLeakedClues: false,
    helpfulClueLeaks: 0,
    totalTokens: 1000,
    totalRawCostCents: 10,
    ...partial,
  };
}

describe("expandMatchups", () => {
  it("builds a full cartesian product by default", () => {
    const m = expandMatchups(["a", "b"]);
    assert.equal(m.length, 4);
  });

  it("can skip self-play", () => {
    const m = expandMatchups(["a", "b"], { includeSelfPlay: false });
    assert.deepEqual(m, [
      { knower: "a", guesser: "b" },
      { knower: "b", guesser: "a" },
    ]);
  });
});

describe("buildSuiteReport", () => {
  it("aggregates matchups and ranks models", () => {
    const rows: SuiteGameRow[] = [
      row({
        id: "1",
        knowerModel: "knower-a",
        guesserModel: "guesser-b",
        outcome: "guesser_correct",
        usedLeakedClues: true,
        helpfulClueLeaks: 2,
      }),
      row({
        id: "2",
        knowerModel: "knower-a",
        guesserModel: "guesser-b",
        outcome: "secret_leaked",
      }),
      row({
        id: "3",
        knowerModel: "knower-safe",
        guesserModel: "guesser-b",
        outcome: "knower_wins",
        totalRawCostCents: 5,
      }),
      row({
        id: "4",
        knowerModel: "knower-safe",
        guesserModel: "guesser-weak",
        outcome: "knower_wins",
        totalRawCostCents: 5,
      }),
    ];

    const report = buildSuiteReport(rows, { gamesPerMatchup: 2 });
    assert.equal(report.totals.games, 4);
    assert.equal(report.totals.guesserCorrect, 1);
    assert.equal(report.totals.secretLeaked, 1);
    assert.equal(report.totals.knowerWins, 2);
    assert.equal(report.totals.clueLeakGames, 1);
    assert.equal(report.totals.leakedClueCount, 2);
    assert.equal(report.totals.totalRawCostCents, 30);

    assert.equal(report.rankings.bestGuesser?.model, "guesser-b");
    assert.equal(report.rankings.bestKnower?.model, "knower-safe");
    assert.equal(report.rankings.bestSecrecy?.model, "knower-safe");
  });
});

describe("formatSuiteMarkdown", () => {
  it("emits tables and ranking section", () => {
    const report = buildSuiteReport(
      [
        row({
          id: "1",
          knowerModel: "composer-2.5",
          guesserModel: "grok-4.5",
          outcome: "guesser_correct",
          usedLeakedClues: true,
          helpfulClueLeaks: 1,
        }),
        row({
          id: "2",
          knowerModel: "grok-4.5",
          guesserModel: "composer-2.5",
          outcome: "knower_wins",
        }),
      ],
      { gamesPerMatchup: 1 },
    );
    const md = formatSuiteMarkdown(report);
    assert.match(md, /## It's Not Jaws — model matrix/);
    assert.match(md, /### Matchup results/);
    assert.match(md, /### Guesser wins/);
    assert.match(md, /### Title leaks/);
    assert.match(md, /### Guesser-reported clue leaks/);
    assert.match(md, /Best guesser/);
    assert.match(md, /Best knower/);
    assert.match(md, /Best at keeping secrets/);
    assert.match(md, /Overall cost/);
  });
});

describe("parseModelList / defaults", () => {
  it("parses csv and keeps the default six models", () => {
    assert.deepEqual(parseModelList("a, b|c\nd"), ["a", "b", "c", "d"]);
    assert.equal(DEFAULT_MATRIX_MODELS.length, 6);
    assert.ok(DEFAULT_MATRIX_MODELS.includes("claude-fable-5"));
    assert.ok(DEFAULT_MATRIX_MODELS.includes("composer-2.5"));
    assert.ok(DEFAULT_MATRIX_MODELS.includes("grok-4.5"));
  });
});
