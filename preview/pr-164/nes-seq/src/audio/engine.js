import { CHANNELS } from "../apu/constants.js";

/**
 * Browser audio engine: AudioWorklet when available, main-thread fallback otherwise.
 */
export class AudioEngine {
  constructor() {
    /** @type {AudioContext|null} */
    this.ctx = null;
    /** @type {AudioWorkletNode|null} */
    this.node = null;
    /** @type {GainNode|null} */
    this.gain = null;
    this.ready = false;
    this.mode = "none"; // "worklet" | "fallback"
    /** @type {((state: {step:number,playing:boolean,recording:boolean}) => void)|null} */
    this.onTransport = null;
    /** @type {import("../sequencer/player.js").NesPlayer|null} */
    this._fallbackPlayer = null;
    /** @type {number|null} */
    this._fallbackTimer = null;
    /** @type {number} */
    this._nextScheduleTime = 0;
  }

  /**
   * @param {{
   *   pattern: object,
   *   instruments: object,
   *   bpm: number,
   * }} songState
   */
  async init(songState) {
    if (this.ctx) return;
    const Ctx = window.AudioContext || window.webkitAudioContext;
    this.ctx = new Ctx({ sampleRate: 44100, latencyHint: "interactive" });
    this.gain = this.ctx.createGain();
    this.gain.gain.value = 0.85;
    this.gain.connect(this.ctx.destination);

    const workletUrl = new URL("./worklet-processor.js", import.meta.url);
    try {
      await this.ctx.audioWorklet.addModule(workletUrl);
      this.node = new AudioWorkletNode(this.ctx, "nes-apu-processor", {
        numberOfInputs: 0,
        numberOfOutputs: 1,
        outputChannelCount: [1],
      });
      this.node.port.onmessage = (event) => {
        const msg = event.data;
        if (msg?.type === "transport" && this.onTransport) {
          this.onTransport(msg);
        }
      };
      this.node.connect(this.gain);
      this.mode = "worklet";
      this.ready = true;
      this.#post({ type: "bpm", value: songState.bpm });
      this.#post({ type: "pattern", pattern: songState.pattern });
      this.#post({ type: "instruments", instruments: songState.instruments });
    } catch (err) {
      console.warn("AudioWorklet unavailable, using fallback scheduler", err);
      await this.#initFallback(songState);
    }

    if (this.ctx.state === "suspended") {
      await this.ctx.resume();
    }
  }

  /**
   * @param {any} songState
   */
  async #initFallback(songState) {
    const { NesApu } = await import("../apu/nesApu.js");
    const { NesPlayer } = await import("../sequencer/player.js");
    const { createTransport, setPlaying } = await import(
      "../sequencer/transport.js"
    );
    const { patternFromJSON } = await import("../sequencer/pattern.js");

    const apu = new NesApu();
    const transport = createTransport({
      bpm: songState.bpm,
      patternLength: songState.pattern.length,
    });
    this._fallbackTransport = transport;
    this._fallbackPlayer = new NesPlayer(apu, {
      pattern: patternFromJSON(songState.pattern),
      transport,
      instruments: songState.instruments,
      sampleRate: this.ctx.sampleRate,
    });
    this._setPlaying = setPlaying;
    this.mode = "fallback";
    this.ready = true;
  }

  async resume() {
    if (this.ctx?.state === "suspended") await this.ctx.resume();
  }

  /**
   * @param {object} patternJson
   */
  setPattern(patternJson) {
    if (this.mode === "worklet") {
      this.#post({ type: "pattern", pattern: patternJson });
    } else if (this._fallbackPlayer) {
      import("../sequencer/pattern.js").then(({ patternFromJSON }) => {
        this._fallbackPlayer.setPattern(patternFromJSON(patternJson));
      });
    }
  }

  /**
   * @param {object} instruments
   */
  setInstruments(instruments) {
    if (this.mode === "worklet") {
      this.#post({ type: "instruments", instruments });
    } else if (this._fallbackPlayer) {
      this._fallbackPlayer.setInstruments(instruments);
    }
  }

  /** @param {number} bpm */
  setBpm(bpm) {
    if (this.mode === "worklet") {
      this.#post({ type: "bpm", value: bpm });
    } else if (this._fallbackTransport) {
      this._fallbackTransport.bpm = bpm;
    }
  }

  play() {
    if (this.mode === "worklet") {
      this.#post({ type: "play" });
      return;
    }
    if (!this._fallbackPlayer || !this.ctx) return;
    this._setPlaying(this._fallbackTransport, true);
    this._fallbackPlayer.onStart();
    this._nextScheduleTime = this.ctx.currentTime + 0.05;
    this.#pumpFallback();
  }

  stop() {
    if (this.mode === "worklet") {
      this.#post({ type: "stop" });
      return;
    }
    if (this._fallbackTimer != null) {
      clearTimeout(this._fallbackTimer);
      this._fallbackTimer = null;
    }
    if (this._fallbackPlayer) {
      this._setPlaying(this._fallbackTransport, false);
      this._fallbackPlayer.allNotesOff();
    }
  }

  /** @param {boolean} value */
  setRecording(value) {
    if (this.mode === "worklet") {
      this.#post({ type: "record", value });
    } else if (this._fallbackTransport) {
      this._fallbackTransport.recording = value;
      if (value) {
        this._setPlaying(this._fallbackTransport, true);
        this._fallbackPlayer.onStart();
        this._nextScheduleTime = this.ctx.currentTime + 0.05;
        this.#pumpFallback();
      }
    }
  }

  /**
   * @param {import("../instruments/macros.js").ChannelId} channel
   * @param {number} midi
   * @param {number} [velocity]
   */
  noteOn(channel, midi, velocity = 12) {
    if (this.mode === "worklet") {
      this.#post({ type: "noteOn", channel, midi, velocity });
    } else {
      this._fallbackPlayer?.noteOn(channel, midi, velocity);
      if (!this._fallbackTransport?.playing) {
        // One-shot preview: schedule a short buffer.
        this.#previewNote(channel, midi, velocity);
      }
    }
  }

  /**
   * @param {import("../instruments/macros.js").ChannelId} channel
   */
  noteOff(channel) {
    if (this.mode === "worklet") {
      this.#post({ type: "noteOff", channel });
    } else {
      this._fallbackPlayer?.noteOff(channel);
    }
  }

  allNotesOff() {
    if (this.mode === "worklet") {
      this.#post({ type: "allNotesOff" });
    } else {
      this._fallbackPlayer?.allNotesOff();
    }
  }

  get currentStep() {
    if (this.mode === "worklet") return null;
    return this._fallbackTransport?.step ?? 0;
  }

  #post(msg) {
    this.node?.port.postMessage(msg);
  }

  #pumpFallback() {
    if (!this.ctx || !this._fallbackPlayer || !this._fallbackTransport?.playing) {
      return;
    }
    const horizon = 0.12;
    const quantum = 0.05;
    const rate = this.ctx.sampleRate;

    while (this._nextScheduleTime < this.ctx.currentTime + horizon) {
      const frames = Math.max(64, Math.floor(quantum * rate));
      const samples = new Float32Array(frames);
      const { steps } = this._fallbackPlayer.render(samples, frames);
      const buffer = this.ctx.createBuffer(1, frames, rate);
      buffer.copyToChannel(samples, 0);
      const src = this.ctx.createBufferSource();
      src.buffer = buffer;
      src.connect(this.gain);
      src.start(this._nextScheduleTime);
      this._nextScheduleTime += frames / rate;

      if (this.onTransport) {
        this.onTransport({
          step: this._fallbackTransport.step,
          playing: this._fallbackTransport.playing,
          recording: this._fallbackTransport.recording,
        });
      }
      void steps;
    }

    this._fallbackTimer = window.setTimeout(() => this.#pumpFallback(), 25);
  }

  /**
   * Preview a single note when transport is stopped (fallback path).
   */
  async #previewNote(channel, midi, velocity) {
    if (!this.ctx || !this._fallbackPlayer) return;
    // Render ~0.35s of the live note.
    const rate = this.ctx.sampleRate;
    const frames = Math.floor(rate * 0.35);
    const samples = new Float32Array(frames);
    this._fallbackPlayer.noteOn(channel, midi, velocity);
    this._fallbackPlayer.render(samples, frames);
    this._fallbackPlayer.noteOff(channel);
    this._fallbackPlayer.allNotesOff();
    const buffer = this.ctx.createBuffer(1, frames, rate);
    buffer.copyToChannel(samples, 0);
    const src = this.ctx.createBufferSource();
    src.buffer = buffer;
    src.connect(this.gain);
    src.start();
  }
}

export { CHANNELS };
