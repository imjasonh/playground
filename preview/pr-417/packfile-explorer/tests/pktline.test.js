import test from "node:test";
import assert from "node:assert/strict";

import {
  decodePktLines,
  demuxSideband,
  encodePktLine,
  flushPkt,
} from "../src/pktline.js";
import { concatBytes, decodeUtf8, encodeUtf8 } from "../src/hex.js";

test("encode/decode round-trips a pkt-line", () => {
  const line = encodePktLine("want abc\n");
  assert.equal(decodeUtf8(line.subarray(0, 4)), "000d");
  const decoded = decodePktLines(line);
  assert.equal(decoded.length, 1);
  assert.equal(decodeUtf8(decoded[0].data), "want abc\n");
});

test("flush and delim packets decode to markers", () => {
  const bytes = concatBytes([flushPkt(), encodeUtf8("0001")]);
  const decoded = decodePktLines(bytes);
  assert.equal(decoded[0].kind, "flush");
  assert.equal(decoded[1].kind, "delim");
});

test("demuxSideband separates pack, progress, and error bands", () => {
  const packLine = encodePktLine(concatBytes([Uint8Array.from([1]), encodeUtf8("PACKDATA")]));
  const progressLine = encodePktLine(concatBytes([Uint8Array.from([2]), encodeUtf8("counting")]));
  const errLine = encodePktLine(concatBytes([Uint8Array.from([3]), encodeUtf8("boom")]));
  const lines = decodePktLines(concatBytes([packLine, progressLine, errLine]));
  const { pack, progress, error } = demuxSideband(lines);
  assert.equal(decodeUtf8(pack), "PACKDATA");
  assert.equal(progress, "counting");
  assert.equal(error, "boom");
});

test("decodePktLines rejects a non-hex length", () => {
  assert.throws(() => decodePktLines(encodeUtf8("zzzzdata")));
});
