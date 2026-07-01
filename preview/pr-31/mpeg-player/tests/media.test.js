import test from "node:test";
import assert from "node:assert/strict";

import {
  TS_PACKET_BYTES,
  clamp,
  findTransportStreamOffset,
  formatBytes,
  formatTime,
  normalizeMediaUrl,
} from "../src/media.js";

function transportStream(packetCount, prefixBytes = 0) {
  const bytes = new Uint8Array(prefixBytes + packetCount * TS_PACKET_BYTES);
  for (let index = 0; index < packetCount; index += 1) {
    bytes[prefixBytes + index * TS_PACKET_BYTES] = 0x47;
  }
  return bytes;
}

test("findTransportStreamOffset identifies aligned TS packets", () => {
  assert.equal(findTransportStreamOffset(transportStream(5)), 0);
  assert.equal(findTransportStreamOffset(transportStream(5, 13)), 13);
});

test("findTransportStreamOffset rejects short and malformed data", () => {
  assert.equal(findTransportStreamOffset(new Uint8Array(100)), -1);
  assert.equal(
    findTransportStreamOffset(new Uint8Array(TS_PACKET_BYTES * 6)),
    -1,
  );
});

test("formatTime formats minute and hour durations", () => {
  assert.equal(formatTime(0), "0:00");
  assert.equal(formatTime(65.9), "1:05");
  assert.equal(formatTime(3661), "1:01:01");
  assert.equal(formatTime(Number.NaN), "0:00");
});

test("formatBytes chooses compact binary units", () => {
  assert.equal(formatBytes(0), "0 B");
  assert.equal(formatBytes(800), "800 B");
  assert.equal(formatBytes(1536), "1.5 KiB");
  assert.equal(formatBytes(12 * 1024 * 1024), "12 MiB");
});

test("normalizeMediaUrl accepts HTTP and rejects unsafe protocols", () => {
  assert.equal(
    normalizeMediaUrl("/clip.ts", "https://example.test/player/"),
    "https://example.test/clip.ts",
  );
  assert.throws(
    () => normalizeMediaUrl("file:///tmp/clip.ts"),
    /Only HTTP and HTTPS/,
  );
  assert.throws(() => normalizeMediaUrl(""), /Enter an MPEG-TS URL/);
});

test("clamp limits values to an inclusive range", () => {
  assert.equal(clamp(-1, 0, 10), 0);
  assert.equal(clamp(4, 0, 10), 4);
  assert.equal(clamp(11, 0, 10), 10);
});
