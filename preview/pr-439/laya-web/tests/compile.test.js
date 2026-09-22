import test from "node:test";
import assert from "node:assert/strict";

import { compileModel } from "../src/compile.js";
import {
  createWordPieceTokenizer,
  kevSpecialIdsFromBundle,
  normalizeBert,
  pretokenizeBert,
} from "../src/tokenizer.js";

test("compileModel throws when the bundle has no ONNX graph", async () => {
  await assert.rejects(
    () =>
      compileModel({
        model: { title: "No graph" },
        files: { "readme.md": new ArrayBuffer(8) },
        backendChoice: "auto",
        detected: { available: false },
      }),
    /no ONNX graph/,
  );
});

test("WordPiece encodes known words and falls back to unk", () => {
  const tok = createWordPieceTokenizer(
    {
      normalizer: { lowercase: true },
      model: {
        unk_token: "[UNK]",
        continuing_subword_prefix: "##",
        vocab: {
          "[UNK]": 0,
          "[CLS]": 1,
          "[SEP]": 2,
          "[MASK]": 3,
          hello: 10,
          world: 11,
          "##ning": 12,
          run: 13,
        },
      },
      added_tokens: [
        { id: 1, content: "[CLS]" },
        { id: 2, content: "[SEP]" },
        { id: 3, content: "[MASK]" },
      ],
    },
    { cls_token: "[CLS]", sep_token: "[SEP]", pad_token: "[PAD]", mask_token: "[MASK]" },
  );
  assert.deepEqual(tok.encode("Hello world"), [10, 11]);
  assert.deepEqual(tok.encode("running"), [13, 12]);
  assert.deepEqual(tok.encode("xyzzy"), [0]);
  assert.equal(tok.ids.mask, 3);
});

test("Bert pretokenizer splits punctuation", () => {
  assert.deepEqual(pretokenizeBert(normalizeBert("Hello, World!", true)), [
    "hello",
    ",",
    "world",
    "!",
  ]);
});

test("kevSpecialIdsFromBundle reads added token ids", () => {
  const ids = kevSpecialIdsFromBundle({
    "added_tokens.json": {
      "<|fim_prefix|>": 151659,
      "<|fim_middle|>": 151660,
      "<|fim_suffix|>": 151661,
      "<|box_start|>": 151672,
      "<|box_end|>": 151673,
    },
  });
  assert.deepEqual(ids, {
    state: 151659,
    question: 151660,
    optOpen: 151672,
    optClose: 151673,
    decide: 151661,
  });
  assert.equal(kevSpecialIdsFromBundle({}), null);
});
