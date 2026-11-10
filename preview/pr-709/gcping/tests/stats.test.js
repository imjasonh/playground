import test from "node:test";
import assert from "node:assert/strict";

import { compareResults, fastestId, median } from "../src/stats.js";

test("median is null for an empty sample", () => {
  assert.equal(median([]), null);
});

test("median is the middle value of an odd sample", () => {
  assert.equal(median([9, 1, 4]), 4);
});

test("median uses the higher central value of an even sample", () => {
  assert.equal(median([10, 1, 2, 3]), 3);
});

test("compareResults sorts missing medians last when sorting by latency", () => {
  const iowa = { id: "us-central1", location: "Iowa", median: 40 };
  const london = { id: "europe-west2", location: "London", median: null };
  const virginia = { id: "us-east4", location: "Northern Virginia", median: 20 };
  const rows = [iowa, london, virginia];
  rows.sort((a, b) => compareResults(a, b, "median", "ascending"));
  assert.deepEqual(
    rows.map((row) => row.id),
    ["us-east4", "us-central1", "europe-west2"],
  );
});

test("compareResults sorts locations alphabetically", () => {
  const iowa = { id: "us-central1", location: "Iowa", median: 40 };
  const london = { id: "europe-west2", location: "London", median: 90 };
  assert.ok(compareResults(iowa, london, "location", "ascending") < 0);
  assert.ok(compareResults(iowa, london, "location", "descending") > 0);
});

test("fastestId is the lowest median with samples", () => {
  const rows = [
    { id: "us-west1", location: "Oregon", median: 80 },
    { id: "us-east4", location: "Northern Virginia", median: 21 },
    { id: "europe-west1", location: "Belgium", median: null },
  ];
  assert.equal(fastestId(rows), "us-east4");
});

test("fastestId is null when no region has a sample", () => {
  assert.equal(
    fastestId([{ id: "global", location: "Global anycast", median: null }]),
    null,
  );
});
