// In-process jsnes driver. The golden screenshots and audio hashes were
// captured from the browser bundle (`dist/jsnes.js`), so this loads that
// same build rather than the package's ESM sources.

import { createRequire } from "node:module";

const require = createRequire(import.meta.url);
// The package is `"type": "module"`, so Node evaluates the UMD bundle as a
// script and the bundle installs itself on `globalThis`. A CommonJS load
// returns the namespace directly. Accept either shape.
const loaded = require("jsnes");
const jsnes = loaded.NES ? loaded : globalThis.jsnes;
const { NES } = jsnes;
if (typeof NES !== "function") {
  throw new Error("jsnes did not export an NES constructor");
}

const WIDTH = 256;
const HEIGHT = 240;
const PIXEL_COUNT = WIDTH * HEIGHT;
const SAMPLE_RATE = 44100;

function pushSample(state, left, right) {
  if (state.length >= state.left.length) {
    const nextLeft = new Int16Array(state.left.length * 2);
    nextLeft.set(state.left);
    state.left = nextLeft;
    const nextRight = new Int16Array(state.right.length * 2);
    nextRight.set(state.right);
    state.right = nextRight;
  }
  let l = left;
  if (l < -1) l = -1;
  else if (l > 1) l = 1;
  let r = right;
  if (r < -1) r = -1;
  else if (r > 1) r = 1;
  state.left[state.length] = (l * 32767) | 0;
  state.right[state.length] = (r * 32767) | 0;
  state.length++;
}

export function createEmulator() {
  const pixels32 = new Uint32Array(PIXEL_COUNT);
  pixels32.fill(0xff000000);
  const audio = {
    left: new Int16Array(65536),
    right: new Int16Array(65536),
    length: 0,
  };

  const nes = new NES({
    onFrame(frameBuffer) {
      for (let i = 0; i < PIXEL_COUNT; i++) {
        // jsnes pixel is 0x00BBGGRR. OR in opaque alpha and store it
        // little-endian so the bytes come out RGBA, matching the old
        // canvas ImageData path.
        pixels32[i] = 0xff000000 | frameBuffer[i];
      }
    },
    onAudioSample(left, right) {
      pushSample(audio, left, right);
    },
    sampleRate: SAMPLE_RATE,
  });

  return {
    loadRom(bytes) {
      audio.length = 0;
      nes.loadROM(bytes);
    },
    runFrames(count) {
      for (let i = 0; i < count; i++) nes.frame();
    },
    pixels() {
      const rgba = Buffer.allocUnsafe(PIXEL_COUNT * 4);
      new Uint32Array(rgba.buffer, rgba.byteOffset, PIXEL_COUNT).set(pixels32);
      return rgba;
    },
    audioHash() {
      let hash = 2166136261 >>> 0;
      for (let i = 0; i < audio.length; i++) {
        const left = audio.left[i] & 0xffff;
        const right = audio.right[i] & 0xffff;
        hash ^= left & 0xff;
        hash = Math.imul(hash, 16777619);
        hash ^= (left >> 8) & 0xff;
        hash = Math.imul(hash, 16777619);
        hash ^= right & 0xff;
        hash = Math.imul(hash, 16777619);
        hash ^= (right >> 8) & 0xff;
        hash = Math.imul(hash, 16777619);
      }
      return { hash: (hash >>> 0).toString(16), samples: audio.length };
    },
    audioWav() {
      const sampleCount = audio.length;
      const dataBytes = sampleCount * 4;
      const wav = Buffer.alloc(44 + dataBytes);
      wav.write("RIFF", 0);
      wav.writeUInt32LE(wav.length - 8, 4);
      wav.write("WAVE", 8);
      wav.write("fmt ", 12);
      wav.writeUInt32LE(16, 16);
      wav.writeUInt16LE(1, 20);
      wav.writeUInt16LE(2, 22);
      wav.writeUInt32LE(SAMPLE_RATE, 24);
      wav.writeUInt32LE(SAMPLE_RATE * 4, 28);
      wav.writeUInt16LE(4, 32);
      wav.writeUInt16LE(16, 34);
      wav.write("data", 36);
      wav.writeUInt32LE(dataBytes, 40);
      let offset = 44;
      for (let i = 0; i < sampleCount; i++) {
        wav.writeInt16LE(audio.left[i], offset);
        wav.writeInt16LE(audio.right[i], offset + 2);
        offset += 4;
      }
      return wav;
    },
  };
}
