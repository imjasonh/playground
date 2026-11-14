import test from "node:test";
import assert from "node:assert/strict";

import { publishedDataUrl } from "../src/published-data.js";

test("a preview page reads scraped data from the published app", () => {
  assert.equal(
    publishedDataUrl("/playground/preview/pr-12/nypd-choppers/", "data/index.json"),
    "/playground/nypd-choppers/data/index.json",
  );
  assert.equal(
    publishedDataUrl("/playground/preview/pr-12/nypd-choppers/index.html", "data/2026-10-12.json"),
    "/playground/nypd-choppers/data/2026-10-12.json",
  );
});

test("production pages stay on their own URL", () => {
  assert.equal(publishedDataUrl("/playground/nypd-choppers/", "data/index.json"), null);
});
