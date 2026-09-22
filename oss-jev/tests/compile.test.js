import test from "node:test";
import assert from "node:assert/strict";

import { compileModel } from "../src/compile.js";
import { getModel } from "../src/models.js";
import {
  createWordPieceTokenizer,
  kevSpecialIdsFromBundle,
  normalizeBert,
  pretokenizeBert,
} from "../src/tokenizer.js";

test("compileModel builds the fixture session on CPU when WebGPU is absent", async () => {
  const compiled = await compileModel({
    model: getModel("fixture"),
    backendChoice: "auto",
    detected: { available: false },
    gpu: undefined,
  });
  assert.equal(compiled.backend, "cpu");
  assert.equal(compiled.session.engine, "fixture");
  const rows = await compiled.session.runLaya({
    n: 1,
    length: 4,
    maxOptions: 2,
    inputIds: BigInt64Array.from([1n, 2n, 2n, 3n]),
    attention: BigInt64Array.from([1n, 1n, 1n, 1n]),
    markerPos: BigInt64Array.from([1n, 3n]),
    markerMask: Uint8Array.from([1, 1]),
    qtype: BigInt64Array.from([0n]),
    tokenCount: 4,
  });
  assert.equal(rows.length, 1);
  assert.equal(rows[0].logits.length, 2);
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
