import test from "node:test";
import assert from "node:assert/strict";
import { webcrypto } from "node:crypto";
import * as pako from "pako";

import { looseObjectBytes, looseObjectPath, loosePreimage } from "../src/looseObject.js";
import { encodeUtf8, bytesToHex } from "../src/hex.js";

test("loosePreimage prepends the git object header", () => {
  const pre = loosePreimage("blob", encodeUtf8("hi"));
  assert.equal(new TextDecoder().decode(pre), "blob 2\0hi");
});

test("looseObjectBytes deflates to a blob git can re-read", async () => {
  const content = encodeUtf8("hello\n");
  const bytes = looseObjectBytes("blob", content, (b) => pako.deflate(b));
  const inflated = pako.inflate(bytes);
  // Re-inflating yields the pre-image, and its sha1 is git's known hello oid.
  const oid = bytesToHex(new Uint8Array(await webcrypto.subtle.digest("SHA-1", inflated)));
  assert.equal(oid, "ce013625030ba8dba906f756967f9e9ca394464a");
});

test("looseObjectPath splits the oid like git's objects dir", () => {
  assert.equal(looseObjectPath("abcdef1234"), "ab/cdef1234");
});
