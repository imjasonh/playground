// On-device translation + text-to-speech helpers for the WebRTC app.
//
// Once captions give us the peer's speech as text, two more browser APIs let us
// go further with no backend of ours:
//
//   * The built-in AI **Translator API** (`Translator.create(...)`) translates
//     text on-device (it downloads a language pack the first time), so a peer's
//     captions can be shown in the local user's language.
//   * The Web Speech API's **SpeechSynthesis** side reads text aloud, so those
//     translated captions can be spoken in a matching voice/language.
//
// The functions here are pure and DOM-free so they can be unit tested under
// Node and reused unchanged in the browser. The actual `Translator`/
// `speechSynthesis` calls live in app.js.

// A small, curated set of languages for the UI picker. Codes are the base
// (ISO 639-1) forms the Translator API expects.
export const COMMON_LANGUAGES = [
  { code: "en", label: "English" },
  { code: "es", label: "Spanish" },
  { code: "fr", label: "French" },
  { code: "de", label: "German" },
  { code: "it", label: "Italian" },
  { code: "pt", label: "Portuguese" },
  { code: "nl", label: "Dutch" },
  { code: "ru", label: "Russian" },
  { code: "zh", label: "Chinese" },
  { code: "ja", label: "Japanese" },
  { code: "ko", label: "Korean" },
  { code: "ar", label: "Arabic" },
  { code: "hi", label: "Hindi" },
];

// Reduce a BCP-47 tag to its base language, lowercased: "en-US" -> "en".
export function baseLanguage(tag) {
  if (typeof tag !== "string") return "";
  const base = tag.trim().toLowerCase().split(/[-_]/)[0];
  return base || "";
}

// True when two tags share a base language (and both are present).
export function sameLanguage(a, b) {
  const x = baseLanguage(a);
  const y = baseLanguage(b);
  return x !== "" && x === y;
}

// Whether an incoming caption in `sourceLang` should be translated to
// `targetLang`: only when a target is chosen and the languages actually differ.
export function shouldTranslate(sourceLang, targetLang) {
  const target = baseLanguage(targetLang);
  const source = baseLanguage(sourceLang);
  if (!target) return false;
  if (!source) return true; // unknown source — worth attempting a translation
  return source !== target;
}

// Feature detection for the built-in Translator / Language Detector APIs and
// the SpeechSynthesis API. Each takes an explicit scope so it's testable.
export function isTranslatorSupported(scope = globalThis) {
  return Boolean(scope && scope.Translator);
}

export function isLanguageDetectorSupported(scope = globalThis) {
  return Boolean(scope && scope.LanguageDetector);
}

export function isSpeechSynthesisSupported(scope = globalThis) {
  return Boolean(scope && scope.speechSynthesis && scope.SpeechSynthesisUtterance);
}

// A stable cache key for a source->target translator pair.
export function translatorKey(sourceLang, targetLang) {
  return `${baseLanguage(sourceLang)}:${baseLanguage(targetLang)}`;
}

// Choose the best SpeechSynthesis voice for `lang` from a list of voices.
// Prefers an exact tag match, then any voice sharing the base language.
export function pickVoice(voices, lang) {
  if (!Array.isArray(voices) || voices.length === 0 || !lang) return null;
  const wanted = String(lang).toLowerCase();
  const base = baseLanguage(lang);
  const exact = voices.find(
    (v) => v && typeof v.lang === "string" && v.lang.toLowerCase() === wanted,
  );
  if (exact) return exact;
  const byBase = voices.find(
    (v) => v && typeof v.lang === "string" && baseLanguage(v.lang) === base,
  );
  return byBase || null;
}
