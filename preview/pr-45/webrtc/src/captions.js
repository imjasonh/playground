// Speech-to-text caption protocol + helpers for the WebRTC app.
//
// The Web Speech API's SpeechRecognition only transcribes the *local*
// microphone, so realtime captions in a two-way call are cooperative: each peer
// runs recognition on their own mic and streams the resulting text to the other
// peer over the data channel. The recognition itself runs on-device (from this
// app's perspective there's no backend of ours), which keeps the whole feature
// consistent with the serverless model.
//
// The functions here are pure and DOM-free so they can be unit tested under
// Node and reused unchanged in the browser.

export const CAPTION_KIND = "caption";

// Keep a single caption line reasonable — recognition can produce very long
// interim strings before it settles.
export const MAX_CAPTION_LENGTH = 240;

// Build the JSON message carrying a caption line. `final` marks a settled
// (non-interim) transcript so the receiver can let it linger, then clear.
// `lang` is the BCP-47 language the speaker was recognized in (e.g. "en-US"),
// which lets the receiver translate it; it's optional for backward
// compatibility with senders that don't tag their language.
export function createCaptionMessage(text, final = false, lang) {
  if (typeof text !== "string") {
    throw new TypeError("createCaptionMessage expects a string");
  }
  const msg = {
    kind: CAPTION_KIND,
    text: text.slice(0, MAX_CAPTION_LENGTH),
    final: Boolean(final),
  };
  if (typeof lang === "string" && lang) msg.lang = lang;
  return msg;
}

// Validate + normalize an incoming caption message. Returns a clean object or
// null when the payload isn't a usable caption.
export function parseCaptionMessage(msg) {
  if (!msg || msg.kind !== CAPTION_KIND) return null;
  if (typeof msg.text !== "string") return null;
  const out = { text: msg.text.slice(0, MAX_CAPTION_LENGTH), final: Boolean(msg.final) };
  if (typeof msg.lang === "string" && msg.lang) out.lang = msg.lang;
  return out;
}

// Return the SpeechRecognition constructor for the given global scope, or null
// when the browser doesn't support it. `webkit`-prefixed in Chrome/Safari.
export function getSpeechRecognition(scope = globalThis) {
  if (!scope) return null;
  return scope.SpeechRecognition || scope.webkitSpeechRecognition || null;
}

export function isSpeechRecognitionSupported(scope = globalThis) {
  return getSpeechRecognition(scope) != null;
}

// Collapse a SpeechRecognitionResultList (from a `result` event) into trimmed
// interim and final transcript strings, starting at `startIndex`
// (`event.resultIndex`). Works on any array-like shaped like the DOM type, so
// it's unit-testable without a browser.
export function collectTranscript(results, startIndex = 0) {
  let interim = "";
  let final = "";
  if (!results || typeof results.length !== "number") {
    return { interim, final };
  }
  for (let i = Math.max(0, startIndex); i < results.length; i += 1) {
    const result = results[i];
    const alt = result && result[0];
    if (!alt || typeof alt.transcript !== "string") continue;
    if (result.isFinal) final += alt.transcript;
    else interim += alt.transcript;
  }
  return { interim: interim.trim(), final: final.trim() };
}
