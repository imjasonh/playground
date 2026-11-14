/**
 * Chooses among the browser's speech synthesis voices.
 */

/**
 * @param {string} tag A BCP 47 language tag.
 * @return {string} The primary language subtag, lowercase.
 */
function primary(tag) {
  return (tag || '').split(/[-_]/)[0].toLowerCase();
}

/**
 * @param {string} tag
 * @return {string} The tag lowercase with `_` as `-`, as some browsers use.
 */
function normalize(tag) {
  return (tag || '').replace(/_/g, '-').toLowerCase();
}

/**
 * Scores how well a voice suits a deck in `lang`. Higher is better.
 *
 * @param {!SpeechSynthesisVoice} voice
 * @param {string} lang
 * @return {number}
 */
function score(voice, lang) {
  let s = 0;
  if (normalize(voice.lang) === normalize(lang)) s += 4;
  if (/natural|neural|premium|enhanced/i.test(voice.name)) s += 3;
  if (/google|online/i.test(voice.name)) s += 1;
  if (voice.default) s += 0.5;
  return s;
}

/**
 * Lists the voices that speak the deck's language, best first. When none do,
 * lists every voice so the deck can still be heard.
 *
 * @param {!Array<!SpeechSynthesisVoice>} voices
 * @param {string} lang
 * @return {!Array<!SpeechSynthesisVoice>}
 */
export function voicesFor(voices, lang) {
  const want = primary(lang);
  const matching = voices.filter((v) => primary(v.lang) === want);
  const list = matching.length ? matching : [...voices];
  return list.sort(
    (a, b) => score(b, lang) - score(a, lang) || a.name.localeCompare(b.name),
  );
}

/**
 * Picks the saved voice if it suits the deck, otherwise the best match.
 *
 * @param {!Array<!SpeechSynthesisVoice>} voices
 * @param {string} lang
 * @param {string=} savedURI
 * @return {?SpeechSynthesisVoice}
 */
export function pickVoice(voices, lang, savedURI = '') {
  const list = voicesFor(voices, lang);
  return list.find((v) => v.voiceURI === savedURI) ?? list[0] ?? null;
}
