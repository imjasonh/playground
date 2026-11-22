import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";

import { normalizeDoc } from "../src/scrape-lib.js";
import { isPartial, partialPuzzles, selectSolves } from "../src/stats.js";

test("bundled sample shows a trend, two long solves, and three partial puzzles", async () => {
  const doc = normalizeDoc(JSON.parse(await readFile(new URL("../sample/stats.json", import.meta.url), "utf8")));
  const partials = partialPuzzles(doc.puzzles, "date");
  assert.deepEqual(
    partials.map((puzzle) => [puzzle.date, puzzle.percentFilled]),
    [
      ["2025-08-11", 20],
      ["2024-04-18", 62],
      ["2023-11-05", 91],
    ],
  );
  assert.equal(partials.every((puzzle) => isPartial(puzzle)), true);
  const { kept, excluded } = selectSolves(doc.puzzles, { hideOutliers: true });
  assert.ok(kept.length > 100);
  assert.ok(excluded.some((row) => row.puzzle.date === "2024-06-03" && row.reason === "outlier"));
  assert.ok(excluded.some((row) => row.puzzle.date === "2025-01-04" && row.reason === "outlier"));
});
