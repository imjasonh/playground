import {
  enableToneChannels,
  startNoiseNote,
  startPulseNote,
  startTriangleNote,
  stopNoiseNote,
  stopPulseNote,
  stopTriangleNote,
} from "../apu/nesApu.js";
import {
  midiToNoisePeriodIndex,
  midiToTimerPeriod,
} from "../apu/notes.js";
import { CHANNELS } from "../apu/constants.js";
import {
  releaseVoice,
  startVoice,
  tickVoice,
} from "../instruments/macros.js";
import { getStep } from "./pattern.js";
import {
  advanceTransport,
  samplesPerTick,
  TICKS_PER_STEP,
} from "./transport.js";

/**
 * @typedef {import("../apu/nesApu.js").NesApu} NesApu
 * @typedef {import("./pattern.js").Pattern} Pattern
 * @typedef {import("./transport.js").TransportState} TransportState
 * @typedef {import("../instruments/macros.js").Instrument} Instrument
 * @typedef {import("../instruments/macros.js").VoiceState} VoiceState
 * @typedef {import("../instruments/macros.js").ChannelId} ChannelId
 */

/**
 * Realtime / offline song player: drives transport, macros, and APU registers.
 */
export class NesPlayer {
  /**
   * @param {NesApu} apu
   * @param {{
   *   pattern: Pattern,
   *   transport: TransportState,
   *   instruments: Record<ChannelId, Instrument>,
   *   sampleRate?: number,
   * }} opts
   */
  constructor(apu, { pattern, transport, instruments, sampleRate = 44100 }) {
    this.apu = apu;
    this.pattern = pattern;
    this.transport = transport;
    this.instruments = instruments;
    this.sampleRate = sampleRate;
    /** @type {Partial<Record<ChannelId, VoiceState>>} */
    this.voices = {};
    /** @type {Partial<Record<ChannelId, number>>} */
    this.holdTicks = {};
    /** @type {Partial<Record<ChannelId, VoiceState>>} */
    this.liveVoices = {};
    /** Sample accumulator for live-macro clocking while stopped. */
    this._liveSampleAcc = 0;
    this.initialized = false;
  }

  /** @param {Pattern} pattern */
  setPattern(pattern) {
    this.pattern = pattern;
    this.transport.patternLength = pattern.length;
  }

  /** @param {Record<ChannelId, Instrument>} instruments */
  setInstruments(instruments) {
    this.instruments = instruments;
  }

  ensureInit() {
    if (this.initialized) return;
    enableToneChannels(this.apu);
    this.initialized = true;
  }

  /**
   * @param {ChannelId} channel
   * @param {number} midi
   * @param {number} [velocity=12]
   */
  noteOn(channel, midi, velocity = 12) {
    this.ensureInit();
    const base = this.instruments[channel];
    const inst = { ...base, volume: velocity & 15 };
    this.liveVoices[channel] = startVoice(inst, midi);
    this.#applyVoice(channel, tickVoice(this.liveVoices[channel]));
  }

  /** @param {ChannelId} channel */
  noteOff(channel) {
    const live = this.liveVoices[channel];
    if (live) releaseVoice(live);
  }

  allNotesOff() {
    for (const ch of CHANNELS) {
      delete this.liveVoices[ch];
      delete this.voices[ch];
      delete this.holdTicks[ch];
      this.#silence(ch);
    }
  }

  /** Fire the current step (call when transport starts). */
  onStart() {
    this.ensureInit();
    this.#fireStep(this.transport.step);
  }

  /**
   * Render `count` samples into `out`.
   * @param {Float32Array} out
   * @param {number} [count=out.length]
   * @returns {{ steps: number[] }}
   */
  render(out, count = out.length) {
    this.ensureInit();
    const rate = this.sampleRate;
    const cyclesPerSample = this.apu.cpuClock / rate;
    /** @type {number[]} */
    const allSteps = [];
    let residual = this.apu.sampleAccumulator;

    for (let i = 0; i < count; i += 1) {
      if (this.transport.playing) {
        const { ticks, steps } = advanceTransport(this.transport, 1, rate);
        let stepsToFire = steps.slice();
        for (let t = 0; t < ticks; t += 1) {
          if (stepsToFire.length > 0 && t === ticks - 1) {
            for (const step of stepsToFire) {
              this.#fireStep(step);
              allSteps.push(step);
            }
            stepsToFire = [];
          }
          this.#tickMacros();
        }
        for (const step of stepsToFire) {
          this.#fireStep(step);
          allSteps.push(step);
          this.#tickMacros();
        }
      } else if (this.#hasLiveVoices()) {
        // Free-run macros at the current BPM tick rate so held notes evolve.
        this._liveSampleAcc += 1;
        const spt = samplesPerTick(this.transport.bpm, rate);
        while (this._liveSampleAcc >= spt) {
          this._liveSampleAcc -= spt;
          this.#tickMacros();
        }
      }

      residual += cyclesPerSample;
      const whole = residual | 0;
      residual -= whole;
      out[i] = this.apu.clock(whole);
    }
    this.apu.sampleAccumulator = residual;
    return { steps: allSteps };
  }

  #hasLiveVoices() {
    for (const ch of CHANNELS) {
      if (this.liveVoices[ch]) return true;
    }
    return false;
  }

  #tickMacros() {
    for (const ch of CHANNELS) {
      if (this.liveVoices[ch]) {
        const params = tickVoice(this.liveVoices[ch]);
        if (!params.active) {
          delete this.liveVoices[ch];
          if (this.voices[ch]) {
            this.#applyVoice(ch, tickVoice(this.voices[ch]));
          } else {
            this.#silence(ch);
          }
        } else {
          this.#applyVoice(ch, params);
        }
        continue;
      }

      if (this.holdTicks[ch] != null) {
        this.holdTicks[ch] -= 1;
        if (this.holdTicks[ch] <= 0 && this.voices[ch]) {
          releaseVoice(this.voices[ch]);
          delete this.holdTicks[ch];
        }
      }

      if (this.voices[ch]) {
        const params = tickVoice(this.voices[ch]);
        if (!params.active) {
          delete this.voices[ch];
          this.#silence(ch);
        } else {
          this.#applyVoice(ch, params);
        }
      }
    }
  }

  /** @param {number} step */
  #fireStep(step) {
    for (const ch of CHANNELS) {
      if (this.liveVoices[ch]) continue;
      const cell = getStep(this.pattern, ch, step);
      if (!cell) continue;
      const inst = this.instruments[ch];
      const volume = cell.velocity != null ? cell.velocity : inst.volume;
      this.voices[ch] = startVoice({ ...inst, volume }, cell.midi);
      const holdSteps = cell.length ?? 1;
      this.holdTicks[ch] = holdSteps * TICKS_PER_STEP;
      this.#applyVoice(ch, tickVoice(this.voices[ch]));
    }
  }

  /**
   * @param {ChannelId} channel
   * @param {{ midi: number, volume: number, duty: number, shortNoise: boolean, active: boolean }} params
   */
  #applyVoice(channel, params) {
    if (!params.active || params.volume <= 0) {
      this.#silence(channel);
      return;
    }
    if (channel === "pulse1" || channel === "pulse2") {
      startPulseNote(this.apu, channel, {
        duty: params.duty,
        volume: params.volume,
        period: midiToTimerPeriod(params.midi),
      });
      return;
    }
    if (channel === "triangle") {
      startTriangleNote(this.apu, {
        period: midiToTimerPeriod(params.midi),
      });
      return;
    }
    startNoiseNote(this.apu, {
      volume: params.volume,
      periodIndex: midiToNoisePeriodIndex(params.midi),
      shortMode: params.shortNoise,
    });
  }

  /** @param {ChannelId} channel */
  #silence(channel) {
    if (channel === "pulse1" || channel === "pulse2") {
      stopPulseNote(this.apu, channel);
    } else if (channel === "triangle") {
      stopTriangleNote(this.apu);
    } else {
      stopNoiseNote(this.apu);
    }
  }
}
