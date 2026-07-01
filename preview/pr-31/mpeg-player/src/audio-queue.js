/**
 * A small planar PCM queue with a streaming linear resampler. Keeping this in
 * the AudioWorklet avoids creating an AudioBufferSourceNode for every MP2 frame
 * and keeps audio scheduling off the main thread.
 */
export class PlanarAudioQueue {
  constructor(outputSampleRate, maxBufferedSeconds = 2) {
    if (!Number.isFinite(outputSampleRate) || outputSampleRate <= 0) {
      throw new TypeError("outputSampleRate must be positive");
    }
    if (!Number.isFinite(maxBufferedSeconds) || maxBufferedSeconds <= 0) {
      throw new TypeError("maxBufferedSeconds must be positive");
    }
    this.outputSampleRate = outputSampleRate;
    this.maxBufferedSeconds = maxBufferedSeconds;
    this.reset();
  }

  reset() {
    this.chunks = [];
    this.readOffset = 0;
    this.availableFrames = 0;
    this.sourceSampleRate = 0;
    this.phase = 0;
    this.underruns = 0;
    this.droppedFrames = 0;
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

    const maximumFrames = Math.ceil(
      this.sourceSampleRate * this.maxBufferedSeconds,
    );
    if (this.availableFrames > maximumFrames) {
      const excess = this.availableFrames - maximumFrames;
      this.#consume(excess);
      this.droppedFrames += excess;
    }
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

      const first = this.chunks[0];
      const sourceIndex = this.readOffset;
      const currentLeft = first.left[sourceIndex];
      const currentRight = first.right[sourceIndex];
      let nextLeft;
      let nextRight;
      if (sourceIndex + 1 < first.left.length) {
        nextLeft = first.left[sourceIndex + 1];
        nextRight = first.right[sourceIndex + 1];
      } else {
        const second = this.chunks[1];
        nextLeft = second.left[0];
        nextRight = second.right[0];
      }
      outputLeft[index] =
        currentLeft + (nextLeft - currentLeft) * this.phase;
      outputRight[index] =
        currentRight + (nextRight - currentRight) * this.phase;
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
