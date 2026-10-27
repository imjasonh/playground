import assert from "node:assert/strict";
import test from "node:test";

import { decodeBase64, menuTitle, textToCopy } from "./base64.js";

test("standard base64 decodes after surrounding whitespace is trimmed", () => {
  assert.equal(decodeBase64("aGVsbG8="), "hello");
  assert.equal(decodeBase64("\n  aGVsbG8=\t"), "hello");
  assert.equal(decodeBase64("YQ=="), "a");
  assert.equal(decodeBase64(Buffer.from("hi🙂", "utf8").toString("base64")), "hi🙂");
});

test("text that is not standard base64 does not decode", () => {
  assert.equal(decodeBase64("hello"), null);
  assert.equal(decodeBase64("aGVs bG8="), null);
  assert.equal(decodeBase64("aGVsbG8"), null);
  assert.equal(decodeBase64("aGVsbG8-"), null);
  assert.equal(decodeBase64("Y==="), null);
  assert.equal(decodeBase64("data"), null);
  assert.equal(decodeBase64("/w=="), null);
  assert.equal(decodeBase64(""), null);
  assert.equal(decodeBase64("   "), null);
  assert.equal(decodeBase64("IA=="), null);
  assert.equal(decodeBase64("Cg=="), null);
  assert.equal(decodeBase64(null), null);
});

test("a short word that is valid base64 still decodes", () => {
  assert.equal(decodeBase64("file"), "~)^");
});

test("the menu title is one line and does not contain the %s token", () => {
  assert.equal(menuTitle("hello"), "hello");
  assert.equal(menuTitle("a\nb"), "a b");
  assert.equal(menuTitle("a\r\nb"), "a b");
  assert.equal(menuTitle("%s"), "%\u200bs");
  assert.equal(menuTitle("100%"), "100%");
});

test("the click copies the shown decode, or decodes again when that is gone", () => {
  assert.equal(textToCopy("ignored", "hello"), "hello");
  assert.equal(textToCopy("YQ==", null), "a");
  assert.equal(textToCopy(" hello ", null), null);
  assert.equal(textToCopy("", null), null);
});
