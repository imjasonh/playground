/**
 * NES APU AudioWorklet processor.
 * Imports the same player/APU modules used by unit tests and WAV export.
 */
import { NesApu } from "../apu/nesApu.js";
import { NesPlayer } from "../sequencer/player.js";
import { createEmptyPattern, patternFromJSON } from "../sequencer/pattern.js";
import {
  createTransport,
  setBpm,
  setPlaying,
  setRecording,
} from "../sequencer/transport.js";
import { createDefaultInstruments } from "../instruments/macros.js";
import { CHANNELS } from "../apu/constants.js";

class NesApuProcessor extends AudioWorkletProcessor {
  constructor() {
    super();
    const defaults = createDefaultInstruments();
    const instruments = {
      pulse1: { ...defaults[0], channel: "pulse1" },
      pulse2: { ...defaults[1], channel: "pulse2" },
      triangle: { ...defaults[3], channel: "triangle" },
      noise: { ...defaults[4], channel: "noise" },
    };

    this.apu = new NesApu();
    this.transport = createTransport({ bpm: 120, patternLength: 16 });
    const pattern = createEmptyPattern(16);
    this.player = new NesPlayer(this.apu, {
      patterns: [pattern],
      order: [0],
      transport: this.transport,
      instruments,
      sampleRate: sampleRate,
    });
    this.buffer = new Float32Array(128);
    this.lastPostedStep = -1;
    this.lastPostedOrder = -1;

    this.port.onmessage = (event) => {
      this.#onMessage(event.data);
    };

    this.port.postMessage({ type: "ready", sampleRate });
  }

  /**
   * @param {unknown} data
   */
  #onMessage(data) {
    if (!data || typeof data !== "object") return;
    const msg = /** @type {any} */ (data);
    switch (msg.type) {
      case "play":
        setPlaying(this.transport, true);
        this.player.onStart();
        break;
      case "stop":
        setPlaying(this.transport, false);
        this.player.allNotesOff();
        this.apu.reset();
        this.player.initialized = false;
        break;
      case "record":
        setRecording(this.transport, Boolean(msg.value));
        if (msg.value) this.player.onStart();
        break;
      case "bpm":
        setBpm(this.transport, msg.value);
        break;
      case "song": {
        const patterns = (msg.patterns || []).map((p) => patternFromJSON(p));
        const order = Array.isArray(msg.order) ? msg.order : [0];
        if (patterns.length) {
          this.player.setSongPatterns(patterns, order);
        }
        break;
      }
      case "instruments":
        this.player.setInstruments(msg.instruments);
        break;
      case "noteOn":
        this.player.noteOn(msg.channel, msg.midi, msg.velocity ?? 12);
        break;
      case "noteOff":
        this.player.noteOff(msg.channel);
        break;
      case "allNotesOff":
        this.player.allNotesOff();
        break;
      default:
        break;
    }
  }

  /**
   * @param {Float32Array[][]} _inputs
   * @param {Float32Array[][]} outputs
   */
  process(_inputs, outputs) {
    const output = outputs[0]?.[0];
    if (!output) return true;

    if (output.length !== this.buffer.length) {
      this.buffer = new Float32Array(output.length);
    }

    const { steps, orderIndex } = this.player.render(
      this.buffer,
      output.length,
    );
    output.set(this.buffer);

    if (this.transport.playing) {
      const step = this.transport.step;
      if (
        step !== this.lastPostedStep ||
        orderIndex !== this.lastPostedOrder ||
        steps.length
      ) {
        this.lastPostedStep = step;
        this.lastPostedOrder = orderIndex;
        this.port.postMessage({
          type: "transport",
          step,
          orderIndex,
          playing: this.transport.playing,
          recording: this.transport.recording,
        });
      }
    }

    return true;
  }
}

registerProcessor("nes-apu-processor", NesApuProcessor);

void CHANNELS;
