import { PlanarAudioQueue } from "./audio-queue.js";

class MpegPcmOutput extends AudioWorkletProcessor {
  constructor() {
    super();
    this.queue = new PlanarAudioQueue(sampleRate);
    this.streamPort = null;
    this.generation = 0;
    this.epoch = 0;
    this.latestSequence = 0;
    this.renderQuanta = 0;

    this.port.onmessage = ({ data }) => {
      if (data?.type === "attach" && data.port) {
        this.#attach(data.port);
      }
    };
  }

  #attach(port) {
    this.streamPort?.close();
    this.streamPort = port;
    this.streamPort.onmessage = ({ data }) => this.#receive(data);
    this.streamPort.start();
  }

  #receive(message) {
    if (message?.type === "reset") {
      this.generation = message.generation;
      this.epoch = message.epoch;
      this.latestSequence = 0;
      this.queue.reset();
      return;
    }

    if (
      message?.type === "samples" &&
      message.generation === this.generation &&
      message.epoch === this.epoch
    ) {
      this.latestSequence = message.sequence;
      this.queue.push(message.sampleRate, message.left, message.right);
    }
  }

  process(_inputs, outputs) {
    const output = outputs[0];
    if (!output || output.length === 0) {
      return true;
    }

    const left = output[0];
    const right = output[1] ?? output[0];
    this.queue.pull(left, right);

    this.renderQuanta += 1;
    if (this.streamPort && this.renderQuanta % 32 === 0) {
      this.streamPort.postMessage({
        type: "telemetry",
        generation: this.generation,
        epoch: this.epoch,
        sequence: this.latestSequence,
        bufferedSeconds: this.queue.bufferedSeconds,
        underruns: this.queue.underruns,
        droppedFrames: this.queue.droppedFrames,
      });
    }
    return true;
  }
}

registerProcessor("mpeg-pcm-output", MpegPcmOutput);
