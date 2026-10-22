import assert from "node:assert/strict";
import { test } from "node:test";
import { diffScreens, normalizeScreen, screensEqual } from "../src/screen.js";

test("normalize trims trailing spaces and blank tail lines", () => {
  assert.equal(normalizeScreen("ab  \ncd\n\n\n"), "ab\ncd");
});

test("screens that differ only in trailing space are equal", () => {
  assert.ok(screensEqual("hello   \nworld", "hello\nworld   "));
  assert.ok(!screensEqual("hello", "world"));
});

test("diff marks lines that left and arrived", () => {
  const diff = diffScreens("one\ntwo\nthree", "one\nTWO\nthree");
  assert.equal(diff, "- two\n+ TWO");
});

test("diff of identical screens is empty", () => {
  assert.equal(diffScreens("same\nlines", "same\nlines"), "");
});

test("diff reports an added bottom line", () => {
  assert.equal(diffScreens("a", "a\nb"), "+ b");
});
