import test from "node:test";
import assert from "node:assert/strict";

import {
  bucketKey,
  bucketLabel,
  chartLayout,
  excludedDates,
  formatDate,
  formatSolveTime,
  formatUnsolvedCount,
  isPartial,
  median,
  medianByWeekday,
  partialPuzzles,
  puzzleUrl,
  selectSolves,
  solvedYears,
  trendByWeekday,
  weekdayName,
} from "../src/stats.js";

function solved(date, seconds) {
  return { date, id: 1, solved: true, percentFilled: 100, seconds };
}

test("weekdayName uses the print date, not the local timezone", () => {
  assert.equal(weekdayName("2024-06-03"), "Monday");
  assert.equal(weekdayName("2024-06-02"), "Sunday");
  assert.equal(weekdayName("2024-02-29"), "Thursday");
});

test("puzzleUrl points at the daily puzzle for that print date", () => {
  assert.equal(
    puzzleUrl("1942-02-15"),
    "https://www.nytimes.com/crosswords/game/daily/1942/02/15",
  );
});

test("formatSolveTime renders minutes and hours", () => {
  assert.equal(formatSolveTime(90), "1:30");
  assert.equal(formatSolveTime(3661), "1:01:01");
  assert.equal(formatSolveTime(0), "");
  assert.equal(formatSolveTime(null), "");
});

test("formatUnsolvedCount names one puzzle and many puzzles", () => {
  assert.equal(formatUnsolvedCount(0), "0 unsolved puzzles.");
  assert.equal(formatUnsolvedCount(1), "1 unsolved puzzle.");
  assert.equal(formatUnsolvedCount(1200), "1,200 unsolved puzzles.");
});

test("formatDate is a calendar date in UTC", () => {
  assert.equal(formatDate("2024-04-18"), "Thursday, April 18, 2024");
});

test("isPartial is a started puzzle that is not solved", () => {
  assert.equal(isPartial({ solved: false, percentFilled: 40 }), true);
  assert.equal(isPartial({ solved: false, percentFilled: 0 }), false);
  assert.equal(isPartial({ solved: true, percentFilled: 100 }), false);
});

test("median averages the two middle values", () => {
  assert.equal(median([10, 30]), 20);
  assert.equal(median([10, 20, 40]), 20);
  assert.equal(median([]), null);
});

test("selectSolves drops a solve that is far above or below that weekday", () => {
  const monday = ["2024-06-03", "2024-06-10", "2024-06-17", "2024-06-24", "2024-07-01"];
  const puzzles = [
    ...monday.map((date) => solved(date, 500)),
    solved("2024-07-08", 18000),
    solved("2024-07-15", 20),
    solved("2024-06-04", 4000),
  ];
  const { kept, excluded } = selectSolves(puzzles, { hideOutliers: true });
  assert.deepEqual(
    excluded.map((row) => row.puzzle.date).sort(),
    ["2024-07-08", "2024-07-15"],
  );
  assert.ok(excluded.every((row) => row.reason === "outlier"));
  assert.ok(kept.some((puzzle) => puzzle.date === "2024-06-04"));
  const medians = medianByWeekday(kept);
  const mondayMedian = medians.find((row) => row.weekday === "Monday");
  assert.equal(mondayMedian.median, 500);
  assert.equal(mondayMedian.count, 5);
});

test("solves before 2014 stay out of the chart range", () => {
  const puzzles = [solved("2013-12-30", 400), solved("2014-01-06", 500), solved("2014-06-02", 600)];
  const { kept, excluded } = selectSolves(puzzles, { fromYear: 2005, throughYear: 2026 });
  assert.deepEqual(
    kept.map((puzzle) => puzzle.date),
    ["2014-01-06", "2014-06-02"],
  );
  assert.deepEqual(excluded, []);
  assert.deepEqual(solvedYears(puzzles), [2014]);
});

test("a listed date stays out even when outliers are shown", () => {
  const puzzles = [solved("2024-06-03", 600), solved("2024-06-10", 9000)];
  const { kept, excluded } = selectSolves(puzzles, {
    hideOutliers: false,
    excludedDates: new Set(["2024-06-03"]),
  });
  assert.deepEqual(
    kept.map((puzzle) => puzzle.date),
    ["2024-06-10"],
  );
  assert.deepEqual(
    excluded.map((row) => [row.puzzle.date, row.reason]),
    [["2024-06-03", "listed"]],
  );
});

test("excludedDates reads print dates from the repo file", () => {
  const dates = excludedDates({ dates: ["2024-06-03", "nope", 12, "2025-01-04"] });
  assert.deepEqual([...dates], ["2024-06-03", "2025-01-04"]);
  assert.equal(excludedDates(null).size, 0);
});

test("partialPuzzles sorts by weekday starting Monday, then by date", () => {
  const puzzles = [
    { date: "2024-06-04", id: 1, solved: false, percentFilled: 10, seconds: null },
    { date: "2024-06-03", id: 2, solved: false, percentFilled: 80, seconds: null },
    { date: "2024-06-02", id: 3, solved: false, percentFilled: 5, seconds: null },
    { date: "2024-06-05", id: 4, solved: true, percentFilled: 100, seconds: 100 },
    { date: "2024-06-06", id: 5, solved: false, percentFilled: 0, seconds: null },
  ];
  const rows = partialPuzzles(puzzles, "weekday");
  assert.deepEqual(
    rows.map((puzzle) => puzzle.date),
    ["2024-06-03", "2024-06-04", "2024-06-02"],
  );
  assert.equal(partialPuzzles(puzzles, "percent")[0].date, "2024-06-03");
});

test("trendByWeekday buckets medians by quarter", () => {
  assert.equal(bucketKey("2024-05-15", "quarter"), "2024-Q2");
  assert.equal(bucketLabel("2024-Q2"), "2024 Q2");
  assert.equal(bucketLabel("2024-05"), "May 2024");
  const puzzles = [
    solved("2024-04-01", 600),
    solved("2024-05-06", 900),
    solved("2024-07-01", 1200),
  ];
  const series = trendByWeekday(puzzles, "quarter");
  const monday = series.find((row) => row.weekday === "Monday");
  assert.deepEqual(
    monday.points.map((point) => [point.bucket, point.median, point.count]),
    [
      ["2024-Q2", 750, 2],
      ["2024-Q3", 1200, 1],
    ],
  );
});

test("chartLayout places later buckets to the right and slower times higher", () => {
  const layout = chartLayout([
    {
      weekday: "Monday",
      points: [
        { bucket: "2024-Q1", median: 600, count: 4 },
        { bucket: "2024-Q2", median: 1200, count: 4 },
      ],
    },
  ]);
  const points = layout.lines[0].points;
  assert.ok(points[1].x > points[0].x);
  assert.ok(points[1].y < points[0].y);
  assert.ok(layout.yTicks.length >= 2);
  assert.equal(layout.xTicks[0].anchor, "start");
  assert.equal(layout.xTicks.at(-1).anchor, "end");
});
