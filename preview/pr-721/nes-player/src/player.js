const WIDTH = 256;
const HEIGHT = 240;
const FRAME_MS = 1000 / 60.0988;
// Past this much catch-up (a background tab, a debugger pause), drop time
// rather than run the game fast.
const MAX_CATCH_UP_MS = 100;
const BATCH = 512;

// Plays the samples the main thread posts. It holds at most MAX_LATENCY
// seconds and drops the oldest past that, so drift between the emulator's
// 60.0988 Hz and the display's refresh can't build up lag.
const WORKLET = `
const MAX_LATENCY = 0.12;
const TARGET_LATENCY = 0.05;
class NesOut extends AudioWorkletProcessor {
  constructor() {
    super();
    this.cap = 1 << 15;
    this.l = new Float32Array(this.cap);
    this.r = new Float32Array(this.cap);
    this.read = 0;
    this.count = 0;
    this.port.onmessage = (e) => {
      if (e.data === "clear") { this.count = 0; return; }
      const { l, r } = e.data;
      for (let i = 0; i < l.length; i++) {
        const w = (this.read + this.count) % this.cap;
        this.l[w] = l[i];
        this.r[w] = r[i];
        if (this.count < this.cap) this.count++;
        else this.read = (this.read + 1) % this.cap;
      }
      if (this.count > sampleRate * MAX_LATENCY) {
        const drop = this.count - Math.floor(sampleRate * TARGET_LATENCY);
        this.read = (this.read + drop) % this.cap;
        this.count -= drop;
      }
    };
  }
  process(_inputs, outputs) {
    const [outL, outR] = outputs[0];
    for (let i = 0; i < outL.length; i++) {
      if (this.count > 0) {
        outL[i] = this.l[this.read];
        outR[i] = this.r[this.read];
        this.read = (this.read + 1) % this.cap;
        this.count--;
      } else {
        outL[i] = 0;
        outR[i] = 0;
      }
    }
    return true;
  }
}
registerProcessor("nes-out", NesOut);
`;

class AudioOut {
  constructor() {
    this.ctx = new AudioContext();
    this.gain = this.ctx.createGain();
    this.gain.connect(this.ctx.destination);
    this.node = null;
    this.l = new Float32Array(BATCH);
    this.r = new Float32Array(BATCH);
    this.n = 0;
    const url = URL.createObjectURL(
      new Blob([WORKLET], { type: "text/javascript" }),
    );
    this.ready = this.ctx.audioWorklet
      .addModule(url)
      .then(() => {
        this.node = new AudioWorkletNode(this.ctx, "nes-out", {
          numberOfInputs: 0,
          outputChannelCount: [2],
        });
        this.node.connect(this.gain);
      })
      .finally(() => URL.revokeObjectURL(url));
  }

  get sampleRate() {
    return this.ctx.sampleRate;
  }

  get suspended() {
    return this.ctx.state === "suspended";
  }

  resume() {
    if (this.suspended) this.ctx.resume().catch(() => {});
  }

  set muted(on) {
    this.gain.gain.value = on ? 0 : 1;
  }

  push = (left, right) => {
    this.l[this.n] = left;
    this.r[this.n] = right;
    if (++this.n === BATCH) this.flush();
  };

  flush() {
    if (this.n === 0) return;
    if (this.node) {
      this.node.port.postMessage({
        l: this.l.slice(0, this.n),
        r: this.r.slice(0, this.n),
      });
    }
    this.n = 0;
  }

  clear() {
    this.n = 0;
    this.node?.port.postMessage("clear");
  }
}

/** Runs one jsnes NES at 60.0988 Hz into a canvas and an AudioContext. */
export class Player {
  /**
   * @param {HTMLCanvasElement} canvas
   * @param {{onError?: (e: Error) => void}} [options]
   */
  constructor(canvas, { onError } = {}) {
    canvas.width = WIDTH;
    canvas.height = HEIGHT;
    this.ctx2d = canvas.getContext("2d", { alpha: false });
    this.image = this.ctx2d.createImageData(WIDTH, HEIGHT);
    this.pixels = new Uint32Array(this.image.data.buffer);
    this.ctx2d.fillStyle = "#000";
    this.ctx2d.fillRect(0, 0, WIDTH, HEIGHT);
    this.onError = onError ?? ((e) => console.error(e));
    this.audio = null;
    this.nes = null;
    this.rom = null;
    this.paused = false;
    this.muted = false;
    this.raf = 0;
    this.last = 0;
    this.acc = 0;
  }

  /**
   * Creates the AudioContext. Call it from a click or key handler so the
   * browser lets it start; outside one it starts suspended until resume().
   */
  unlockAudio() {
    if (!this.audio && typeof AudioContext !== "undefined") {
      this.audio = new AudioOut();
      this.audio.muted = this.muted;
    }
    this.audio?.resume();
  }

  get audioBlocked() {
    return Boolean(this.audio?.suspended);
  }

  /** @param {Uint8Array} bytes */
  load(bytes) {
    this.stop();
    this.unlockAudio();
    const audio = this.audio;
    const nes = new globalThis.jsnes.NES({
      onFrame: (frame) => {
        const px = this.pixels;
        for (let i = 0; i < px.length; i++) px[i] = 0xff000000 | frame[i];
      },
      onAudioSample: audio ? audio.push : () => {},
      sampleRate: audio ? audio.sampleRate : 48000,
      emulateSound: Boolean(audio),
    });
    nes.loadROM(bytes);
    this.nes = nes;
    this.rom = bytes;
    this.paused = false;
    this.start();
  }

  reset() {
    if (this.rom) this.load(this.rom);
  }

  setPaused(paused) {
    if (!this.nes) return;
    this.paused = paused;
    if (paused) this.stop();
    else this.start();
  }

  setMuted(muted) {
    this.muted = muted;
    if (this.audio) this.audio.muted = muted;
  }

  buttonDown(player, button) {
    this.nes?.buttonDown(player, button);
  }

  buttonUp(player, button) {
    this.nes?.buttonUp(player, button);
  }

  start() {
    if (this.raf || !this.nes) return;
    this.last = 0;
    this.acc = 0;
    this.raf = requestAnimationFrame(this.tick);
  }

  stop() {
    if (this.raf) cancelAnimationFrame(this.raf);
    this.raf = 0;
    this.audio?.clear();
  }

  tick = (now) => {
    this.raf = requestAnimationFrame(this.tick);
    if (this.last) this.acc += Math.min(now - this.last, MAX_CATCH_UP_MS);
    else this.acc = FRAME_MS;
    this.last = now;
    let ran = false;
    try {
      while (this.acc >= FRAME_MS) {
        this.nes.frame();
        this.acc -= FRAME_MS;
        ran = true;
      }
    } catch (e) {
      this.stop();
      this.nes = null;
      this.onError(e);
      return;
    }
    if (ran) {
      this.audio?.flush();
      this.ctx2d.putImageData(this.image, 0, 0);
    }
  };
}
