import test from "node:test";
import assert from "node:assert/strict";

import { detectImage, imageDataUrl, toBase64 } from "../src/imagePreview.js";
import { encodeUtf8 } from "../src/hex.js";

test("detectImage recognizes common magic bytes", () => {
  assert.equal(detectImage(Uint8Array.from([0x89, 0x50, 0x4e, 0x47, 0x0d])), "image/png");
  assert.equal(detectImage(Uint8Array.from([0xff, 0xd8, 0xff, 0xe0])), "image/jpeg");
  assert.equal(detectImage(Uint8Array.from([0x47, 0x49, 0x46, 0x38, 0x39])), "image/gif");
  const webp = Uint8Array.from([0x52, 0x49, 0x46, 0x46, 0, 0, 0, 0, 0x57, 0x45, 0x42, 0x50]);
  assert.equal(detectImage(webp), "image/webp");
  assert.equal(detectImage(encodeUtf8('<svg xmlns="…"></svg>')), "image/svg+xml");
});

test("detectImage returns null for non-images", () => {
  assert.equal(detectImage(encodeUtf8("just some text")), null);
});

test("toBase64 matches Buffer for varied lengths", () => {
  for (const s of ["", "a", "ab", "abc", "abcd", "hello world"]) {
    const bytes = encodeUtf8(s);
    assert.equal(toBase64(bytes), Buffer.from(bytes).toString("base64"));
  }
});

test("imageDataUrl builds a data URL for an image", () => {
  const png = Uint8Array.from([0x89, 0x50, 0x4e, 0x47, 1, 2, 3]);
  assert.ok(imageDataUrl(png).startsWith("data:image/png;base64,"));
  assert.equal(imageDataUrl(encodeUtf8("nope")), null);
});
