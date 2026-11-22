/**
 * Moves through a deck: narrates the current slide and, while playing,
 * advances when the narration ends.
 *
 * Events:
 * - `slide`: `detail` is `{index}` after the current slide changes.
 * - `cue`, `word`: forwarded from the narrator, with `slide` added to
 *   `detail`.
 * - `state`: `detail` is `{playing}` when playback starts or stops.
 * - `finished`: the last slide's narration ended.
 */
export class Player extends EventTarget {
  /**
   * @param {!import('./deck.js').Deck} deck
   * @param {!import('./narrator.js').Narrator} narrator
   * @param {{
   *   timer?: {setTimeout: Function, clearTimeout: Function},
   *   gapMs?: number,
   *   holdMs?: number,
   * }=} options
   */
  constructor(
    deck,
    narrator,
    {timer = globalThis, gapMs = 700, holdMs = 3000} = {},
  ) {
    super();
    this.deck = deck;
    this.narrator = narrator;
    this.timer = timer;
    /** Pause between one slide's narration and the next slide. */
    this.gapMs = gapMs;
    /** How long a slide without notes stays up during playback. */
    this.holdMs = holdMs;
    this.index = 0;
    this.playing = false;
    /** Whether the current slide's narration has finished. */
    this.done = false;
    this.wait = null;

    this.forward = (e) =>
      this.dispatchEvent(
        new CustomEvent(e.type, {detail: {...e.detail, slide: this.index}}),
      );
    this.onEnd = () => this.slideEnded();
    narrator.addEventListener('cue', this.forward);
    narrator.addEventListener('word', this.forward);
    narrator.addEventListener('end', this.onEnd);
  }

  /** Detaches from the narrator and stops it. */
  dispose() {
    this.cancelWait();
    this.narrator.stop();
    this.narrator.removeEventListener('cue', this.forward);
    this.narrator.removeEventListener('word', this.forward);
    this.narrator.removeEventListener('end', this.onEnd);
  }

  /** @return {number} */
  get count() {
    return this.deck.slides.length;
  }

  /** @return {!Array<string>} The current slide's cues. */
  get cues() {
    return this.deck.slides[this.index]?.cues ?? [];
  }

  play() {
    if (this.playing || !this.count) return;
    this.setPlaying(true);
    if (this.done) {
      this.goTo(this.index >= this.count - 1 ? 0 : this.index + 1);
    } else if (this.narrator.active && this.narrator.paused) {
      this.narrator.resume();
    } else {
      this.narrate(0);
    }
  }

  pause() {
    if (!this.playing) return;
    this.setPlaying(false);
    this.cancelWait();
    this.narrator.pause();
  }

  toggle() {
    if (this.playing) {
      this.pause();
    } else {
      this.play();
    }
  }

  /**
   * Shows slide `index`. While playing, narration starts there.
   *
   * @param {number} index
   */
  goTo(index) {
    const next = Math.max(0, Math.min(index, this.count - 1));
    this.cancelWait();
    this.narrator.stop();
    this.done = false;
    this.index = next;
    this.dispatchEvent(new CustomEvent('slide', {detail: {index: next}}));
    if (this.playing) this.narrate(0);
  }

  next() {
    this.goTo(this.index + 1);
  }

  prev() {
    this.goTo(this.index - 1);
  }

  /**
   * Plays the current slide from cue `cue`.
   *
   * @param {number} cue
   */
  playCue(cue) {
    this.cancelWait();
    this.done = false;
    this.setPlaying(true);
    this.narrate(cue);
  }

  /** @param {number} rate */
  setRate(rate) {
    this.narrator.setRate(rate);
  }

  /** @param {number} from */
  narrate(from) {
    const cues = this.cues;
    if (cues.length) {
      this.narrator.start(cues, from);
      return;
    }
    this.narrator.stop();
    this.wait = this.timer.setTimeout(() => {
      this.wait = null;
      this.slideEnded();
    }, this.holdMs / this.narrator.rate);
  }

  slideEnded() {
    this.done = true;
    if (!this.playing) return;
    if (this.index >= this.count - 1) {
      this.setPlaying(false);
      this.dispatchEvent(new Event('finished'));
      return;
    }
    this.wait = this.timer.setTimeout(() => {
      this.wait = null;
      this.next();
    }, this.gapMs / this.narrator.rate);
  }

  cancelWait() {
    if (this.wait !== null) {
      this.timer.clearTimeout(this.wait);
      this.wait = null;
    }
  }

  /** @param {boolean} playing */
  setPlaying(playing) {
    if (this.playing === playing) return;
    this.playing = playing;
    this.dispatchEvent(new CustomEvent('state', {detail: {playing}}));
  }
}
