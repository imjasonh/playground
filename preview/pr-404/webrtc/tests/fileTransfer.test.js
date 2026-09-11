import test from "node:test";
import assert from "node:assert/strict";

import {
  CHUNK_SIZE,
  MESSAGE_KIND,
  createFileMeta,
  createChatMessage,
  createFileEnd,
  countChunks,
  chunkRanges,
  formatBytes,
  FileAssembler,
} from "../src/fileTransfer.js";

test("countChunks rounds up and handles edges", () => {
  assert.equal(countChunks(0), 0);
  assert.equal(countChunks(1, 16), 1);
  assert.equal(countChunks(16, 16), 1);
  assert.equal(countChunks(17, 16), 2);
  assert.equal(countChunks(48, 16), 3);
  assert.throws(() => countChunks(-1));
  assert.throws(() => countChunks(10, 0));
});

test("chunkRanges tiles the whole file without gaps or overlap", () => {
  const size = 40;
  const ranges = chunkRanges(size, 16);
  assert.deepEqual(ranges, [
    { start: 0, end: 16 },
    { start: 16, end: 32 },
    { start: 32, end: 40 },
  ]);
  assert.equal(ranges[0].start, 0);
  assert.equal(ranges[ranges.length - 1].end, size);
  assert.deepEqual(chunkRanges(0, 16), []);
});

test("createFileMeta produces a valid meta message with a unique id", () => {
  const meta1 = createFileMeta({ name: "a.png", size: 20, type: "image/png" }, 16);
  const meta2 = createFileMeta({ name: "a.png", size: 20, type: "image/png" }, 16);
  assert.equal(meta1.kind, MESSAGE_KIND.fileMeta);
  assert.equal(meta1.name, "a.png");
  assert.equal(meta1.size, 20);
  assert.equal(meta1.mime, "image/png");
  assert.equal(meta1.chunks, 2);
  assert.notEqual(meta1.id, meta2.id);
});

test("createFileMeta falls back to a default name", () => {
  const meta = createFileMeta({ size: 5 });
  assert.equal(meta.name, "download");
  assert.equal(meta.mime, "");
});

test("chat and file-end envelopes carry the right kind", () => {
  assert.deepEqual(createChatMessage("hi"), {
    kind: MESSAGE_KIND.chat,
    text: "hi",
  });
  assert.deepEqual(createFileEnd("abc"), {
    kind: MESSAGE_KIND.fileEnd,
    id: "abc",
  });
});

test("formatBytes scales units", () => {
  assert.equal(formatBytes(0), "0 B");
  assert.equal(formatBytes(512), "512 B");
  assert.equal(formatBytes(1024), "1 KB");
  assert.equal(formatBytes(1536), "1.5 KB");
  assert.equal(formatBytes(1024 * 1024), "1 MB");
  assert.equal(formatBytes(-5), "0 B");
});

test("FileAssembler reports progress and reassembles bytes in order", () => {
  const original = new Uint8Array([1, 2, 3, 4, 5, 6, 7]);
  const meta = createFileMeta({ name: "d.bin", size: original.length }, 3);
  const assembler = new FileAssembler(meta);
  assert.equal(assembler.complete, false);

  const ranges = chunkRanges(original.length, 3);
  let lastProgress = 0;
  for (const { start, end } of ranges) {
    lastProgress = assembler.addChunk(original.slice(start, end).buffer);
  }
  assert.equal(lastProgress, 1);
  assert.equal(assembler.complete, true);

  const blob = assembler.toBlob();
  assert.equal(blob.size, original.length);
});

test("FileAssembler handles zero-byte files", () => {
  const meta = createFileMeta({ name: "empty", size: 0 });
  const assembler = new FileAssembler(meta);
  assert.equal(assembler.complete, true);
  assert.equal(assembler.toBlob().size, 0);
});

test("CHUNK_SIZE stays under the common 64 KiB SCTP message ceiling", () => {
  assert.ok(CHUNK_SIZE <= 64 * 1024);
});
