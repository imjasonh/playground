import test from "node:test";
import assert from "node:assert/strict";

import { publishedDataUrl } from "../src/published-data.js";

test("a preview page reads scraped data from the published app", () => {
  assert.equal(
    publishedDataUrl("/playground/preview/pr-570/nyt-crossword/", "data/stats.json"),
    "/playground/nyt-crossword/data/stats.json",
  );
  assert.equal(
    publishedDataUrl("/playground/preview/pr-570/nyt-crossword/index.html", "data/stats.json"),
    "/playground/nyt-crossword/data/stats.json",
  );
  assert.equal(
    publishedDataUrl("/preview/pr-3/nypd-choppers/", "data/index.json"),
    "/nypd-choppers/data/index.json",
  );
});

test("production pages and non-data files stay on their own URL", () => {
  assert.equal(publishedDataUrl("/playground/nyt-crossword/", "data/stats.json"), null);
  assert.equal(publishedDataUrl("/playground/preview/pr-570", "data/stats.json"), null);
  assert.equal(
    publishedDataUrl("/playground/preview/pr-570/nyt-crossword/", "sample/stats.json"),
    null,
  );
});
