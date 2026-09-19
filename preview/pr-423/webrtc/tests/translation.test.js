import test from "node:test";
import assert from "node:assert/strict";

import {
  COMMON_LANGUAGES,
  baseLanguage,
  sameLanguage,
  shouldTranslate,
  isTranslatorSupported,
  isLanguageDetectorSupported,
  isSpeechSynthesisSupported,
  translatorKey,
  pickVoice,
} from "../src/translation.js";

test("COMMON_LANGUAGES entries have a code and label", () => {
  assert.ok(COMMON_LANGUAGES.length > 5);
  for (const lang of COMMON_LANGUAGES) {
    assert.equal(typeof lang.code, "string");
    assert.equal(typeof lang.label, "string");
    assert.match(lang.code, /^[a-z]{2}$/);
  }
});

test("baseLanguage reduces BCP-47 tags to the base language", () => {
  assert.equal(baseLanguage("en-US"), "en");
  assert.equal(baseLanguage("ES"), "es");
  assert.equal(baseLanguage("zh_Hans_CN"), "zh");
  assert.equal(baseLanguage(""), "");
  assert.equal(baseLanguage(null), "");
});

test("sameLanguage compares base languages", () => {
  assert.equal(sameLanguage("en-US", "en-GB"), true);
  assert.equal(sameLanguage("en", "es"), false);
  assert.equal(sameLanguage("", "en"), false);
});

test("shouldTranslate only when a target is set and languages differ", () => {
  assert.equal(shouldTranslate("en-US", "es"), true);
  assert.equal(shouldTranslate("en-US", "en"), false);
  assert.equal(shouldTranslate("en-US", ""), false);
  // Unknown source is still worth attempting when a target is chosen.
  assert.equal(shouldTranslate("", "es"), true);
  assert.equal(shouldTranslate(null, ""), false);
});

test("feature detectors read the given scope", () => {
  assert.equal(isTranslatorSupported({ Translator: {} }), true);
  assert.equal(isTranslatorSupported({}), false);
  assert.equal(isLanguageDetectorSupported({ LanguageDetector: {} }), true);
  assert.equal(isLanguageDetectorSupported({}), false);
  assert.equal(
    isSpeechSynthesisSupported({ speechSynthesis: {}, SpeechSynthesisUtterance: function () {} }),
    true,
  );
  assert.equal(isSpeechSynthesisSupported({ speechSynthesis: {} }), false);
  assert.equal(isSpeechSynthesisSupported({}), false);
});

test("translatorKey is stable and base-normalized", () => {
  assert.equal(translatorKey("en-US", "es-ES"), "en:es");
  assert.equal(translatorKey("EN", "ES"), "en:es");
});

test("pickVoice prefers an exact tag then a base-language match", () => {
  const voices = [
    { name: "A", lang: "en-GB" },
    { name: "B", lang: "es-ES" },
    { name: "C", lang: "es-MX" },
  ];
  assert.equal(pickVoice(voices, "es-MX").name, "C");
  assert.equal(pickVoice(voices, "es").name, "B");
  assert.equal(pickVoice(voices, "fr"), null);
  assert.equal(pickVoice([], "es"), null);
  assert.equal(pickVoice(voices, ""), null);
});
