import test from "node:test";
import assert from "node:assert/strict";

import {
  buildFetchRequest,
  parseInfoRefs,
  splitUploadPackResult,
} from "../src/protocol.js";
import { decodePktLines, demuxSideband, encodePktLine, flushPkt } from "../src/pktline.js";
import { concatBytes, decodeUtf8, encodeUtf8 } from "../src/hex.js";

const OID_A = "1".repeat(40);
const OID_B = "2".repeat(40);

test("parseInfoRefs reads refs, capabilities, and HEAD symref", () => {
  const advert = concatBytes([
    encodePktLine("# service=git-upload-pack\n"),
    flushPkt(),
    encodePktLine(`${OID_A} HEAD\0multi_ack symref=HEAD:refs/heads/main ofs-delta\n`),
    encodePktLine(`${OID_A} refs/heads/main\n`),
    encodePktLine(`${OID_B} refs/heads/dev\n`),
    flushPkt(),
  ]);
  const parsed = parseInfoRefs(advert);
  assert.equal(parsed.refs.length, 3);
  assert.ok(parsed.capabilities.includes("ofs-delta"));
  assert.equal(parsed.head, OID_A);
});

test("buildFetchRequest puts capabilities on the first want and ends with done", () => {
  const body = buildFetchRequest({ wants: [OID_A, OID_B], deepen: 1 });
  const text = decodeUtf8(body);
  assert.match(text, /want 1{40} multi_ack_detailed/);
  assert.match(text, /want 2{40}\n/);
  assert.match(text, /deepen 1\n/);
  assert.match(text, /0009done\n$/);
});

test("splitUploadPackResult separates control lines from side-band pack data", () => {
  const packLine = encodePktLine(concatBytes([Uint8Array.from([1]), encodeUtf8("PACK...")]));
  const result = concatBytes([
    encodePktLine(`shallow ${OID_A}\n`),
    flushPkt(),
    encodePktLine("NAK\n"),
    packLine,
  ]);
  const { control, sidebandLines } = splitUploadPackResult(result);
  assert.ok(control.some((c) => c.startsWith("shallow")));
  const { pack } = demuxSideband(sidebandLines);
  assert.equal(decodeUtf8(pack), "PACK...");
});
