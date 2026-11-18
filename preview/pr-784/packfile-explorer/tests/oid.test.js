import test from "node:test";
import assert from "node:assert/strict";
import { createHash } from "node:crypto";

import { loosePreimage, makeComputeOid } from "../src/oid.js";
import { decodeUtf8, encodeUtf8 } from "../src/hex.js";

const computeOid = makeComputeOid((bytes) =>
  new Uint8Array(createHash("sha1").update(Buffer.from(bytes)).digest()),
);

test("loosePreimage prepends the git object header", () => {
  const pre = loosePreimage("blob", encodeUtf8("abc"));
  assert.equal(decodeUtf8(pre.subarray(0, 7)), "blob 3\0");
});

test("computeOid matches git's well-known empty blob oid", async () => {
  const oid = await computeOid("blob", new Uint8Array(0));
  assert.equal(oid, "e69de29bb2d1d6434b8b29ae775ad8c2e48c5391");
});

test("computeOid matches git's 'hello\\n' blob oid", async () => {
  const oid = await computeOid("blob", encodeUtf8("hello\n"));
  assert.equal(oid, "ce013625030ba8dba906f756967f9e9ca394464a");
});
