import test from "node:test";
import assert from "node:assert/strict";

import {
  CAPTION_KIND,
  MAX_CAPTION_LENGTH,
  createCaptionMessage,
  parseCaptionMessage,
  getSpeechRecognition,
  isSpeechRecognitionSupported,
  collectTranscript,
} from "../src/captions.js";

test("createCaptionMessage carries the kind, text, and final flag", () => {
  assert.deepEqual(createCaptionMessage("hello", true), {
    kind: CAPTION_KIND,
    text: "hello",
    final: true,
  });
  assert.equal(createCaptionMessage("hi").final, false);
  assert.throws(() => createCaptionMessage(42));
});

test("caption text is clamped to a max length", () => {
  const long = "a".repeat(MAX_CAPTION_LENGTH + 50);
  assert.equal(createCaptionMessage(long).text.length, MAX_CAPTION_LENGTH);
});

test("parseCaptionMessage validates and normalizes incoming payloads", () => {
  const msg = createCaptionMessage("hey there", true);
  assert.deepEqual(parseCaptionMessage(msg), { text: "hey there", final: true });
  assert.equal(parseCaptionMessage(null), null);
  assert.equal(parseCaptionMessage({ kind: "chat", text: "x" }), null);
  assert.equal(parseCaptionMessage({ kind: CAPTION_KIND, text: 5 }), null);
  assert.equal(parseCaptionMessage({ kind: CAPTION_KIND, text: "x" }).final, false);
});

test("getSpeechRecognition finds either the standard or webkit constructor", () => {
  function Std() {}
  function Webkit() {}
  assert.equal(getSpeechRecognition({ SpeechRecognition: Std }), Std);
  assert.equal(getSpeechRecognition({ webkitSpeechRecognition: Webkit }), Webkit);
  // Prefer the unprefixed one when both exist.
  assert.equal(
    getSpeechRecognition({ SpeechRecognition: Std, webkitSpeechRecognition: Webkit }),
    Std,
  );
  assert.equal(getSpeechRecognition({}), null);
  assert.equal(getSpeechRecognition(null), null);
});

test("isSpeechRecognitionSupported reflects availability", () => {
  assert.equal(isSpeechRecognitionSupported({ SpeechRecognition: function () {} }), true);
  assert.equal(isSpeechRecognitionSupported({}), false);
});

// A helper that mimics the shape of a SpeechRecognitionResultList entry.
function result(transcript, isFinal) {
  return { 0: { transcript }, length: 1, isFinal };
}

test("collectTranscript splits interim from final and trims", () => {
  const results = [result("hello ", true), result("world", false)];
  results.length = 2;
  const { interim, final } = collectTranscript(results, 0);
  assert.equal(final, "hello");
  assert.equal(interim, "world");
});

test("collectTranscript honors the start index", () => {
  const results = [result("skip me ", true), result("keep this", false)];
  results.length = 2;
  const { interim, final } = collectTranscript(results, 1);
  assert.equal(final, "");
  assert.equal(interim, "keep this");
});

test("collectTranscript tolerates empty or malformed input", () => {
  assert.deepEqual(collectTranscript(null), { interim: "", final: "" });
  assert.deepEqual(collectTranscript([]), { interim: "", final: "" });
  const bad = [{ isFinal: true }];
  bad.length = 1;
  assert.deepEqual(collectTranscript(bad), { interim: "", final: "" });
});
