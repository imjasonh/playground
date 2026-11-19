import test from "node:test";
import assert from "node:assert/strict";

import {
  createServerProgress,
  describeTransfer,
  formatElapsed,
  formatRate,
  parseGitProgressLine,
  tidyServerProgress,
} from "../src/fetchActivity.js";

test("parseGitProgressLine reads a counting update and a finished enumerating line", () => {
  assert.deepEqual(parseGitProgressLine("remote: Counting objects:  40% (12/30)"), {
    stage: "counting",
    label: "Counting objects",
    percent: 40,
    done: 12,
    total: 30,
    finished: false,
  });
  const done = parseGitProgressLine("Enumerating objects: 30, done.");
  assert.equal(done.stage, "enumerating");
  assert.equal(done.done, 30);
  assert.equal(done.finished, true);
  assert.equal(parseGitProgressLine("Total 30 (delta 10), reused 0 (delta 0)").stage, "total");
  assert.equal(parseGitProgressLine("remote: "), null);
});

test("createServerProgress keeps the latest carriage-return update", () => {
  const progress = createServerProgress();
  progress.push("Counting objects:   4% (1/25)\r");
  progress.push("Counting objects:  80% (20/25)\rCounting objects: 100% (25/25), done.\n");
  const current = progress.current();
  assert.equal(current.stage, "counting");
  assert.equal(current.percent, 100);
  assert.equal(current.finished, true);

  // A chunk that ends in the middle of the next percentage is not a count of 1.
  progress.push("Compressing objects:  1");
  assert.equal(progress.current().stage, "counting");
  progress.push("2% (3/25)\r");
  assert.equal(progress.current().stage, "compressing");
  assert.equal(progress.current().percent, 12);
});

test("tidyServerProgress turns overwrites into separate lines", () => {
  assert.equal(tidyServerProgress("Counting objects:  1% (1/2)\rCounting objects: 100% (2/2), done.\n"),
    "Counting objects:  1% (1/2)\nCounting objects: 100% (2/2), done.");
});

test("describeTransfer prefers the server phase, then bytes received", () => {
  const server = { stage: "counting", label: "Counting objects", percent: 40, done: 12, total: 30, finished: false };
  const early = describeTransfer({ server, bytes: 200, totalBytes: 5_000_000, elapsedMs: 1500, scope: "all 12 branches" });
  assert.equal(early.text, "Counting objects, 40%");
  assert.equal(early.done, 40);
  assert.equal(early.total, 100);
  assert.match(early.detail, /12 of 30/);

  const downloading = describeTransfer({
    server,
    bytes: 2_500_000,
    totalBytes: 5_000_000,
    elapsedMs: 2000,
    scope: "all 12 branches",
  });
  assert.equal(downloading.text, "Downloading all 12 branches, 2.4 MiB of 4.8 MiB");
  assert.equal(downloading.done, 2_500_000);
  assert.equal(downloading.total, 5_000_000);
  assert.match(downloading.detail, /\/s/);

  const unknown = describeTransfer({ server: null, bytes: 800_000, totalBytes: null, elapsedMs: 2000, scope: "the default branch (main)" });
  assert.equal(unknown.text, "Downloading the default branch (main), 781 KiB");
  assert.equal(unknown.total, null);
});

test("formatElapsed and formatRate stay blank before they mean something", () => {
  assert.equal(formatElapsed(400), "");
  assert.equal(formatElapsed(1500), "1s");
  assert.equal(formatElapsed(65_000), "1:05");
  assert.equal(formatRate(1000, 100), "");
  assert.match(formatRate(1024 * 1024, 1000), /1\.0 MiB\/s/);
});
