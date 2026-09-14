import test from "node:test";
import assert from "node:assert/strict";
import { createHash } from "node:crypto";

import * as pako from "pako";
import { parsePack, resolveObjects } from "../src/pack.js";
import { makePakoInflate } from "../src/inflate.js";
import { makeComputeOid } from "../src/oid.js";
import { decodeUtf8 } from "../src/hex.js";
import { buildAppendDelta, buildPack, oidOf } from "./synthPack.js";

const inflate = makePakoInflate(pako);
const computeOid = makeComputeOid((bytes) =>
  new Uint8Array(createHash("sha1").update(Buffer.from(bytes)).digest()),
);

test("parsePack reads the header and entry offsets", () => {
  const { pack } = buildPack([{ type: "blob", content: "hello\n" }]);
  const parsed = parsePack(pack, inflate);
  assert.equal(parsed.version, 2);
  assert.equal(parsed.count, 1);
  assert.equal(parsed.objects[0].offset, 12);
  assert.equal(decodeUtf8(parsed.objects[0].data), "hello\n");
});

test("resolveObjects resolves an ofs-delta chain and computes oids", async () => {
  const base = "line one\nline two\n";
  const target = `${base}line three\n`;
  const delta = buildAppendDelta(base, "line three\n");
  const { pack } = buildPack([
    { type: "blob", content: base },
    { type: "ofs-delta", delta, baseIndex: 0 },
  ]);

  const parsed = parsePack(pack, inflate);
  const { objects, contentByOid } = await resolveObjects(parsed, computeOid);

  const baseOid = oidOf("blob", base);
  const targetOid = oidOf("blob", target);
  assert.equal(objects[0].oid, baseOid);
  assert.equal(objects[1].oid, targetOid);
  assert.equal(objects[1].deltaType, "ofs");
  assert.equal(objects[1].depth, 1);
  assert.equal(objects[1].baseOid, baseOid);
  assert.equal(decodeUtf8(contentByOid.get(targetOid)), target);
});

test("resolveObjects resolves a ref-delta against a base earlier in the pack", async () => {
  const base = "alpha\nbravo\n";
  const target = `${base}charlie\n`;
  const delta = buildAppendDelta(base, "charlie\n");
  const baseOid = oidOf("blob", base);
  const { pack } = buildPack([
    { type: "blob", content: base },
    { type: "ref-delta", delta, baseOid },
  ]);

  const parsed = parsePack(pack, inflate);
  const { byOid, contentByOid } = await resolveObjects(parsed, computeOid);

  const targetOid = oidOf("blob", target);
  assert.ok(byOid.has(targetOid), "target resolved");
  assert.equal(byOid.get(targetOid).deltaType, "ref");
  assert.equal(decodeUtf8(contentByOid.get(targetOid)), target);
});

test("a ref-delta with an unknown base is reported as unresolved (thin pack)", async () => {
  const delta = buildAppendDelta("x", "y");
  const { pack } = buildPack([
    { type: "ref-delta", delta, baseOid: "0".repeat(40) },
  ]);
  const parsed = parsePack(pack, inflate);
  const { unresolved } = await resolveObjects(parsed, computeOid);
  assert.equal(unresolved.length, 1);
  assert.equal(unresolved[0].baseOid, "0".repeat(40));
});
