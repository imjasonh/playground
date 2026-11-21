/**
 * Speaks a list of cues one after another with the Web Speech API.
 *
 * Events:
 * - `cue`: `detail` is `{index, text}` when a cue starts.
 * - `word`: `detail` is `{index, charIndex, charLength}` on a word boundary,
 *   for voices that report them.
 * - `end`: the last cue finished.
 * - `speecherror`: `detail` is `{error}` when the synthesizer fails a cue. The
 *   narrator shows that cue for its estimated length instead.
 *
 * When muted, or when the browser has no speech synthesis, each cue is shown
 * for as long as a voice would take to say it, so captions still advance.
 */
import {estimateMs} from './script.js';

/** Chrome's network voices go silent after about 15 seconds without this. */
const KEEPALIVE_MS = 10000;

export class Narrator extends EventTarget {
  /**
   * @param {{
   *   synth?: ?SpeechSynthesis,
   *   Utterance?: ?Function,
   *   timer?: {setTimeout: Function, clearTimeout: Function,
   *            setInterval: Function, clearInterval: Function},
   * }=} options
   */
  constructor({
    synth = globalThis.speechSynthesis ?? null,
    Utterance = globalThis.SpeechSynthesisUtterance ?? null,
    timer = globalThis,
  } = {}) {
    super();
    this.synth = synth;
    this.Utterance = Utterance;
    this.timer = timer;
    this.rate = 1;
    this.lang = 'en-US';
    /** @type {?SpeechSynthesisVoice} */
    this.voice = null;
    this.muted = !synth || !Utterance;
    /** @type {!Array<string>} */
    this.cues = [];
    this.index = 0;
    this.active = false;
    this.paused = false;
    this.token = 0;
    this.timeout = null;
    this.keepalive = null;
    /** Held so Chrome doesn't collect it and drop its `end` event. */
    this.utterance = null;
  }

  /** @return {boolean} Whether speech synthesis is available at all. */
  get canSpeak() {
    return Boolean(this.synth && this.Utterance);
  }

  /**
   * Starts speaking `cues` at `from`, replacing anything in progress.
   *
   * @param {!Array<string>} cues
   * @param {number=} from
   */
  start(cues, from = 0) {
    this.halt();
    this.cues = cues;
    this.index = Math.max(0, Math.min(from, cues.length));
    this.active = true;
    this.paused = false;
    this.speakCurrent();
  }

  /** Stops speaking and remembers the current cue. */
  pause() {
    if (!this.active || this.paused) return;
    this.paused = true;
    this.halt();
  }

  /** Speaks the paused cue again from its start. */
  resume() {
    if (!this.active || !this.paused) return;
    this.paused = false;
    this.speakCurrent();
  }

  stop() {
    this.halt();
    this.active = false;
    this.paused = false;
  }

  /** @param {number} rate */
  setRate(rate) {
    this.rate = rate;
    this.restart();
  }

  /** @param {?SpeechSynthesisVoice} voice */
  setVoice(voice) {
    this.voice = voice;
    this.restart();
  }

  /** @param {boolean} muted */
  setMuted(muted) {
    this.muted = muted || !this.canSpeak;
    this.restart();
  }

  /** Says the current cue again so a new setting takes effect. */
  restart() {
    if (!this.active || this.paused) return;
    this.halt();
    this.speakCurrent();
  }

  /** Cancels speech and timers; late events from them are ignored. */
  halt() {
    this.token++;
    this.clearTimers();
    if (this.utterance) {
      this.utterance = null;
      this.synth.cancel();
    }
  }

  clearTimers() {
    if (this.timeout !== null) {
      this.timer.clearTimeout(this.timeout);
      this.timeout = null;
    }
    if (this.keepalive !== null) {
      this.timer.clearInterval(this.keepalive);
      this.keepalive = null;
    }
  }

  speakCurrent() {
    const token = ++this.token;
    if (this.index >= this.cues.length) {
      this.active = false;
      this.dispatchEvent(new Event('end'));
      return;
    }
    const index = this.index;
    const text = this.cues[index];
    this.dispatchEvent(new CustomEvent('cue', {detail: {index, text}}));
    if (this.muted) {
      this.showFor(token, estimateMs(text, this.rate));
      return;
    }

    const u = new this.Utterance(text);
    u.rate = this.rate;
    u.lang = this.voice?.lang || this.lang;
    if (this.voice) u.voice = this.voice;
    u.onboundary = (e) => {
      if (token !== this.token || e.name === 'sentence') return;
      this.dispatchEvent(
        new CustomEvent('word', {
          detail: {index, charIndex: e.charIndex, charLength: e.charLength},
        }),
      );
    };
    u.onend = () => this.advance(token);
    u.onerror = (e) => {
      if (token !== this.token) return;
      if (e.error === 'interrupted' || e.error === 'canceled') return;
      this.utterance = null;
      this.clearTimers();
      this.dispatchEvent(
        new CustomEvent('speecherror', {detail: {error: e.error}}),
      );
      this.showFor(token, estimateMs(text, this.rate));
    };
    this.utterance = u;

    // If the synthesizer drops the utterance without an end or error event,
    // move on rather than stall the deck.
    this.timeout = this.timer.setTimeout(
      () => this.advance(token),
      estimateMs(text, this.rate) * 2.5 + 4000,
    );
    if (this.voice && this.voice.localService === false) {
      this.keepalive = this.timer.setInterval(() => {
        if (token !== this.token || !this.synth.speaking) return;
        this.synth.pause();
        this.synth.resume();
      }, KEEPALIVE_MS);
    }
    if (this.synth.paused) this.synth.resume();
    this.synth.speak(u);
  }

  /**
   * @param {number} token
   * @param {number} ms
   */
  showFor(token, ms) {
    this.timeout = this.timer.setTimeout(() => this.advance(token), ms);
  }

  /** @param {number} token */
  advance(token) {
    if (token !== this.token) return;
    this.clearTimers();
    this.utterance = null;
    this.index++;
    this.speakCurrent();
  }
}
