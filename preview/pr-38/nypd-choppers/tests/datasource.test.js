import test from "node:test";
import assert from "node:assert/strict";

import { resolveDataBase } from "../src/datasource.js";

const ORIGIN = "https://imjasonh.github.io";

test("production path reads its own data directory", () => {
  assert.equal(
    resolveDataBase(ORIGIN, "/playground/nypd-choppers/"),
    "https://imjasonh.github.io/playground/nypd-choppers/data",
  );
});

test("a trailing index.html is ignored when resolving the directory", () => {
  assert.equal(
    resolveDataBase(ORIGIN, "/playground/nypd-choppers/index.html"),
    "https://imjasonh.github.io/playground/nypd-choppers/data",
  );
});

test("a PR preview strips the preview segment to reuse production data", () => {
  assert.equal(
    resolveDataBase(ORIGIN, "/playground/preview/pr-38/nypd-choppers/"),
    "https://imjasonh.github.io/playground/nypd-choppers/data",
  );
  assert.equal(
    resolveDataBase(ORIGIN, "/playground/preview/pr-7/nypd-choppers/index.html"),
    "https://imjasonh.github.io/playground/nypd-choppers/data",
  );
});

test("only the preview segment is stripped, not similarly named paths", () => {
  assert.equal(
    resolveDataBase(ORIGIN, "/playground/preview-notes/nypd-choppers/"),
    "https://imjasonh.github.io/playground/preview-notes/nypd-choppers/data",
  );
});

test("local dev at the site root resolves to a relative-ish data path", () => {
  assert.equal(
    resolveDataBase("http://localhost:3000", "/"),
    "http://localhost:3000/data",
  );
});

test("tolerates a missing/empty pathname", () => {
  assert.equal(resolveDataBase(ORIGIN, ""), "https://imjasonh.github.io/data");
  assert.equal(resolveDataBase(ORIGIN, undefined), "https://imjasonh.github.io/data");
});
