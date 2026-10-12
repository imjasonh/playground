import test from "node:test";
import assert from "node:assert/strict";

import {
  addDays,
  applyPlayTime,
  cookieHeader,
  cookieValue,
  dateChunks,
  gameDataOf,
  idBatches,
  listUrl,
  mergeListed,
  needsGameFetch,
  normalizeDoc,
  puzzlesEqual,
  serializeStats,
  stateUrl,
  todayInNewYork,
} from "../src/scrape-lib.js";

const solved = {
  date: "2024-06-03",
  id: 10,
  solved: true,
  percentFilled: 100,
  seconds: 480,
};

test("addDays crosses months and leap day", () => {
  assert.equal(addDays("2020-02-27", 2), "2020-02-29");
  assert.equal(addDays("2024-12-31", 1), "2025-01-01");
});

test("dateChunks are 100-day inclusive windows that cover the range", () => {
  const chunks = dateChunks("2020-01-01", "2020-06-01");
  assert.equal(chunks[0][0], "2020-01-01");
  assert.equal(chunks[0][1], addDays("2020-01-01", 99));
  assert.equal(chunks.at(-1)[1], "2020-06-01");
  for (let i = 1; i < chunks.length; i += 1) {
    assert.equal(chunks[i][0], addDays(chunks[i - 1][1], 1));
  }
  assert.deepEqual(dateChunks("2024-06-03", "2024-06-03"), [["2024-06-03", "2024-06-03"]]);
});

test("todayInNewYork follows the evening the job runs", () => {
  assert.equal(todayInNewYork(new Date("2026-10-13T01:17:00Z")), "2026-10-12");
  assert.equal(todayInNewYork(new Date("2026-01-15T01:17:00Z")), "2026-01-14");
});

test("listUrl asks for daily puzzles in print-date order", () => {
  const url = listUrl("2024-01-01", "2024-04-09");
  assert.equal(url.origin, "https://www.nytimes.com");
  assert.equal(url.pathname, "/svc/crosswords/v3/puzzles.json");
  assert.equal(url.searchParams.get("publish_type"), "daily");
  assert.equal(url.searchParams.get("sort_by"), "print_date");
  assert.equal(url.searchParams.get("date_start"), "2024-01-01");
  assert.equal(url.searchParams.get("date_end"), "2024-04-09");
});

test("cookieValue accepts the raw NYT-S value or a Cookie assignment", () => {
  assert.equal(cookieValue("  abc  "), "abc");
  assert.equal(cookieValue("NYT-S=abc"), "abc");
  assert.equal(cookieHeader("abc"), "NYT-S=abc");
});

test("needsGameFetch skips a solved puzzle that already has a time", () => {
  const listed = { ...solved, seconds: null };
  assert.equal(needsGameFetch(solved, listed), false);
  assert.equal(needsGameFetch(null, listed), true);
  assert.equal(needsGameFetch({ ...solved, seconds: null }, listed), true);
  assert.equal(
    needsGameFetch(null, { ...listed, solved: false, percentFilled: 0 }),
    false,
  );
  assert.equal(
    needsGameFetch(
      { ...solved, solved: false, percentFilled: 40, seconds: null },
      { ...listed, solved: false, percentFilled: 40 },
    ),
    true,
  );
  assert.equal(
    needsGameFetch(solved, { ...listed, solved: false, percentFilled: 12 }),
    false,
  );
});

test("mergeListed does not refetch a finished game when the list disagrees", () => {
  const listed = [
    {
      print_date: solved.date,
      puzzle_id: solved.id,
      publish_type: "Daily",
      solved: false,
      percent_filled: 15,
    },
  ];
  const { puzzles, fetchList } = mergeListed([solved], listed, {
    start: "2024-01-01",
    end: "2024-12-31",
  });
  assert.equal(fetchList.length, 0);
  assert.equal(puzzles[0].solved, true);
  assert.equal(puzzles[0].seconds, 480);
});

test("mergeListed keeps history outside the requested range", () => {
  const previous = [
    solved,
    {
      date: "2025-01-06",
      id: 11,
      solved: false,
      percentFilled: 20,
      seconds: null,
    },
  ];
  const listed = [
    {
      print_date: "2025-01-06",
      puzzle_id: 11,
      publish_type: "Daily",
      solved: true,
      percent_filled: 100,
    },
  ];
  const { puzzles, fetchList } = mergeListed(previous, listed, {
    start: "2025-01-01",
    end: "2025-01-31",
  });
  assert.deepEqual(
    puzzles.map((puzzle) => puzzle.date),
    ["2024-06-03", "2025-01-06"],
  );
  assert.equal(puzzles[0].seconds, 480);
  assert.deepEqual(
    fetchList.map((puzzle) => puzzle.date),
    ["2025-01-06"],
  );
});

test("stateUrl batches puzzle ids on the crossword state endpoint", () => {
  const url = stateUrl([24534, 24522]);
  assert.equal(url.origin, "https://www.nytimes.com");
  assert.equal(url.pathname, "/svc/games/state/crossword_daily/latests");
  assert.equal(url.searchParams.get("puzzle_ids"), "24534,24522");
  assert.deepEqual(idBatches([1, 2, 3, 4, 5], 2), [
    [1, 2],
    [3, 4],
    [5],
  ]);
});

test("applyPlayTime reads playTimeSeconds and leaves an open puzzle untimed", () => {
  const open = applyPlayTime(
    { ...solved, solved: false, seconds: null, percentFilled: 10 },
    { playTimeSeconds: 90, firstSolve: 0 },
  );
  assert.equal(open.solved, false);
  assert.equal(open.percentFilled, 10);
  assert.equal(open.seconds, null);
  const stillFinished = applyPlayTime(solved, { playTimeSeconds: 90, firstSolve: 0 });
  assert.equal(stillFinished.solved, true);
  assert.equal(stillFinished.seconds, 480);
  const done = applyPlayTime(
    { ...solved, seconds: null, solved: true },
    { playTimeSeconds: 512, firstSolve: 1717200000 },
  );
  assert.equal(done.seconds, 512);
  assert.equal(done.solved, true);
  assert.deepEqual(gameDataOf({ puzzle_id: 1, game_data: { playTimeSeconds: 12 } }), {
    playTimeSeconds: 12,
  });
});

test("serializeStats is stable when the puzzle rows do not change", () => {
  const doc = { generatedAt: "2026-01-15T01:17:00.000Z", puzzles: [solved] };
  const text = serializeStats(doc);
  const again = serializeStats(normalizeDoc(JSON.parse(text)));
  assert.equal(again, text);
  assert.equal(puzzlesEqual(normalizeDoc(JSON.parse(text)).puzzles, [solved]), true);
});
