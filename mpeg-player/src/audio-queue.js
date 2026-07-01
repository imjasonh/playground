/**
 * A small planar PCM queue with a streaming linear resampler. Keeping this in
 * the AudioWorklet avoids creating an AudioBufferSourceNode for every MP2 frame
 * and keeps audio scheduling off the main thread.
 */
export class PlanarAudioQueue {
  constructor(outputSampleRate) {
    if (!Number.isFinite(outputSampleRate) || outputSampleRate <= 0) {
      throw new TypeError("outputSampleRate must be positive");
    }
    this.outputSampleRate = outputSampleRate;
    this.reset();
  }

  reset() {
    this.chunks = [];
    this.readOffset = 0;
    this.availableFrames = 0;
    this.sourceSampleRate = 0;
    this.phase = 0;
    this.underruns = 0;
  }

  get bufferedSeconds() {
    return this.sourceSampleRate
      ? this.availableFrames / this.sourceSampleRate
      : 0;
  }

  push(sourceSampleRate, left, right) {
    if (!Number.isFinite(sourceSampleRate) || sourceSampleRate <= 0) {
      return false;
    }
    if (
      !(left instanceof Float32Array) ||
      !(right instanceof Float32Array) ||
      left.length === 0 ||
      left.length !== right.length
    ) {
      return false;
    }

    if (
      this.sourceSampleRate !== 0 &&
      this.sourceSampleRate !== sourceSampleRate
    ) {
      this.reset();
    }

    this.sourceSampleRate = sourceSampleRate;
    this.chunks.push({ left, right });
    this.availableFrames += left.length;
    return true;
  }

  /**
   * Fills one Web Audio render quantum. Returns the number of non-silent
   * output frames written; the remainder is explicitly zeroed.
   */
  pull(outputLeft, outputRight) {
    outputLeft.fill(0);
    outputRight.fill(0);

    if (!this.sourceSampleRate) {
      return 0;
    }

    const ratio = this.sourceSampleRate / this.outputSampleRate;
    let rendered = 0;

    for (let index = 0; index < outputLeft.length; index += 1) {
      // Linear interpolation requires the current and following source frame.
      if (this.availableFrames < 2) {
        this.underruns += 1;
        break;
      }

      const current = this.#peek(0);
      const next = this.#peek(1);
      outputLeft[index] =
        current.left + (next.left - current.left) * this.phase;
      outputRight[index] =
        current.right + (next.right - current.right) * this.phase;
      rendered += 1;

      this.phase += ratio;
      const consumed = Math.floor(this.phase);
      if (consumed > 0) {
        this.phase -= consumed;
        this.#consume(consumed);
      }
    }

    return rendered;
  }

  #peek(distance) {
    const first = this.chunks[0];
    const index = this.readOffset + distance;
    if (index < first.left.length) {
      return { left: first.left[index], right: first.right[index] };
    }

    const second = this.chunks[1];
    const secondIndex = index - first.left.length;
    return {
      left: second.left[secondIndex],
      right: second.right[secondIndex],
    };
  }

  #consume(count) {
    let remaining = Math.min(count, this.availableFrames);
    this.availableFrames -= remaining;

    while (remaining > 0 && this.chunks.length > 0) {
      const first = this.chunks[0];
      const inChunk = first.left.length - this.readOffset;
      if (remaining < inChunk) {
        this.readOffset += remaining;
        return;
      }

      remaining -= inChunk;
      this.chunks.shift();
      this.readOffset = 0;
    }
  }
}
