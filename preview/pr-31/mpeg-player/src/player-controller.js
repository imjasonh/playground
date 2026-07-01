import {
  TS_PACKET_BYTES,
  TS_PROBE_PACKETS,
  findTransportStreamOffset,
} from "./media.js";

const SOURCE_READY_TIMEOUT = 15_000;
const CHUNK_TIMEOUT = 30_000;
export const MAX_MEDIA_BYTES = 256 * 1024 * 1024;

function assertMediaSize(bytes) {
  if (bytes > MAX_MEDIA_BYTES) {
    throw new Error(
      "This player limits sources to 256 MiB to keep browser memory bounded.",
    );
  }
}

function safeDecodePathSegment(pathName) {
  const segment = pathName.split("/").pop();
  if (!segment) {
    return "Remote MPEG stream";
  }
  try {
    return decodeURIComponent(segment);
  } catch {
    return segment;
  }
}

function deferred(timeoutMilliseconds, message) {
  let resolve;
  let reject;
  const promise = new Promise((resolvePromise, rejectPromise) => {
    resolve = resolvePromise;
    reject = rejectPromise;
  });
  const timer = setTimeout(() => reject(new Error(message)), timeoutMilliseconds);
  return {
    promise,
    resolve(value) {
      clearTimeout(timer);
      resolve(value);
    },
    reject(error) {
      clearTimeout(timer);
      reject(error);
    },
  };
}

function transferableBuffer(view) {
  if (view.byteOffset === 0 && view.byteLength === view.buffer.byteLength) {
    return view.buffer;
  }
  return view.slice().buffer;
}

async function readProbe(reader) {
  const targetBytes = TS_PACKET_BYTES * TS_PROBE_PACKETS;
  const chunks = [];
  let total = 0;
  let done = false;

  while (total < targetBytes && !done) {
    const result = await reader.read();
    done = result.done;
    if (result.value?.byteLength) {
      chunks.push(result.value);
      total += result.value.byteLength;
    }
  }

  if (chunks.length === 1) {
    return { bytes: chunks[0], done };
  }

  const bytes = new Uint8Array(total);
  let offset = 0;
  for (const chunk of chunks) {
    bytes.set(chunk, offset);
    offset += chunk.byteLength;
  }
  return { bytes, done };
}

export class MpegPlayerController extends EventTarget {
  constructor(canvas) {
    super();
    this.canvas = canvas;
    this.worker = null;
    this.initialized = null;
    this.initializedWaiter = null;
    this.sourceWaiters = new Map();
    this.chunkWaiters = new Map();
    this.reader = null;
    this.fetchAbortController = null;
    this.loadId = 0;
    this.chunkId = 0;
    this.state = "idle";
    this.duration = 0;
    this.currentTime = 0;
    this.metadata = null;
    this.audioContext = null;
    this.audioNode = null;
    this.gainNode = null;
    this.audioInitialization = null;
    this.fatalError = null;
    this.volume = 0.85;
    this.muted = false;

    const AudioContext = window.AudioContext || window.webkitAudioContext;
    this.audioCapable = Boolean(
      AudioContext &&
        window.AudioWorkletNode &&
        window.MessageChannel,
    );
  }

  async init() {
    if (this.initialized) {
      return this.initialized;
    }

    this.initialized = this.#initialize();
    return this.initialized;
  }

  async #initialize() {
    if (typeof Worker !== "function") {
      throw new Error("This browser does not support Web Workers.");
    }
    if (typeof WebAssembly !== "object") {
      throw new Error("This browser does not support WebAssembly.");
    }
    if (typeof this.canvas.transferControlToOffscreen !== "function") {
      throw new Error(
        "This browser does not support worker-driven OffscreenCanvas rendering.",
      );
    }

    this.worker = new Worker(new URL("./decoder-worker.js", import.meta.url));
    this.worker.onmessage = ({ data }) => this.#receive(data);
    this.worker.onerror = (event) => {
      event.preventDefault();
      const error = new Error(
        `${event.message || "The decoder worker crashed."} Reload the page to recover.`,
      );
      this.fatalError = error;
      this.state = "error";
      this.#rejectPending(error);
      this.#emit("error", { message: error.message });
      this.#emit("statechange", { state: this.state });
    };
    this.worker.onmessageerror = () => {
      this.#emit("error", {
        message: "The decoder worker returned an unreadable message.",
      });
    };

    this.initializedWaiter = deferred(
      SOURCE_READY_TIMEOUT,
      "The decoder worker did not initialize.",
    );
    const offscreen = this.canvas.transferControlToOffscreen();
    this.worker.postMessage(
      {
        type: "init",
        canvas: offscreen,
        audioCapable: this.audioCapable,
      },
      [offscreen],
    );
    const capabilities = await this.initializedWaiter.promise;
    this.#emit("capabilities", {
      ...capabilities,
      audio: this.audioCapable,
    });
    return capabilities;
  }

  async loadFile(file) {
    if (!(file instanceof Blob) || typeof file.stream !== "function") {
      throw new TypeError("Choose a local MPEG-TS file.");
    }
    assertMediaSize(file.size);
    return this.#loadStream(file.stream(), {
      name: file.name || "Local MPEG stream",
      size: file.size,
    });
  }

  async loadUrl(url) {
    await this.init();
    await this.#cancelTransfer();
    this.fetchAbortController = new AbortController();

    let response;
    try {
      response = await fetch(url, {
        signal: this.fetchAbortController.signal,
        mode: "cors",
      });
    } catch (error) {
      if (error.name === "AbortError") {
        throw error;
      }
      throw new Error(
        "The URL could not be fetched. The server must allow cross-origin requests.",
      );
    }

    if (!response.ok || !response.body) {
      throw new Error(`The media request failed with HTTP ${response.status}.`);
    }

    const pathName = new URL(response.url || url).pathname;
    const name = safeDecodePathSegment(pathName);
    const size = Number(response.headers.get("content-length")) || 0;
    try {
      assertMediaSize(size);
    } catch (error) {
      this.fetchAbortController.abort();
      throw error;
    }
    return this.#loadStream(response.body, { name, size }, false);
  }

  async #loadStream(stream, source, cancelExisting = true) {
    await this.init();
    if (cancelExisting) {
      await this.#cancelTransfer();
    }
    if (this.fatalError) {
      throw this.fatalError;
    }

    const loadId = ++this.loadId;
    this.state = "loading";
    this.duration = 0;
    this.currentTime = 0;
    this.metadata = null;
    this.#emit("statechange", { state: this.state });
    this.#emit("loadprogress", { loaded: 0, total: source.size });

    const sourceWaiter = deferred(
      SOURCE_READY_TIMEOUT,
      "The WebAssembly decoder did not become ready.",
    );
    this.sourceWaiters.set(loadId, sourceWaiter);
    this.worker.postMessage({ type: "load", loadId, ...source });

    const reader = stream.getReader();
    this.reader = reader;

    try {
      await sourceWaiter.promise;
      if (loadId !== this.loadId) {
        return;
      }

      const probe = await readProbe(reader);
      const packetOffset = findTransportStreamOffset(probe.bytes);
      if (packetOffset < 0) {
        throw new Error(
          "This is not a supported MPEG transport stream (MPEG-1 video with optional MP2 audio).",
        );
      }

      let loaded = probe.bytes.byteLength;
      assertMediaSize(loaded);
      await this.#sendChunk(loadId, probe.bytes, loaded, source.size);
      this.#emit("loadprogress", { loaded, total: source.size });

      let done = probe.done;
      while (!done && loadId === this.loadId) {
        const result = await reader.read();
        done = result.done;
        if (!result.value?.byteLength) {
          continue;
        }

        loaded += result.value.byteLength;
        assertMediaSize(loaded);
        await this.#sendChunk(loadId, result.value, loaded, source.size);
        this.#emit("loadprogress", { loaded, total: source.size });
      }

      if (loadId !== this.loadId) {
        return;
      }
      this.worker.postMessage({ type: "complete", loadId });
    } catch (error) {
      if (loadId === this.loadId && error.name !== "AbortError") {
        this.worker.postMessage({ type: "cancel", loadId });
        this.state = "error";
        this.#emit("statechange", { state: this.state });
        this.#emit("error", { message: error.message });
      }
      throw error;
    } finally {
      if (this.reader === reader) {
        this.reader = null;
      }
      reader.releaseLock();
    }
  }

  #sendChunk(loadId, bytes, loaded, total) {
    const chunkId = ++this.chunkId;
    const waiter = deferred(CHUNK_TIMEOUT, "The decoder stopped accepting data.");
    const key = `${loadId}:${chunkId}`;
    this.chunkWaiters.set(key, waiter);
    const buffer = transferableBuffer(bytes);
    this.worker.postMessage(
      { type: "chunk", loadId, chunkId, buffer, loaded, total },
      [buffer],
    );
    return waiter.promise;
  }

  async play() {
    await this.init();
    const loadId = this.loadId;
    await this.#ensureAudio();
    if (this.audioContext?.state === "suspended") {
      await this.audioContext.resume();
    }
    if (loadId !== this.loadId || this.fatalError) {
      return false;
    }
    this.worker.postMessage({ type: "play", loadId });
    return true;
  }

  pause() {
    this.worker?.postMessage({ type: "pause", loadId: this.loadId });
  }

  seek(time) {
    this.worker?.postMessage({ type: "seek", loadId: this.loadId, time });
  }

  setVolume(value) {
    this.volume = Math.min(1, Math.max(0, Number(value) || 0));
    this.#applyGain();
  }

  setMuted(muted) {
    this.muted = Boolean(muted);
    this.#applyGain();
  }

  async #ensureAudio() {
    if (!this.audioCapable) {
      return false;
    }
    if (this.audioInitialization) {
      return this.audioInitialization;
    }

    this.audioInitialization = this.#initializeAudio().catch((error) => {
      this.audioCapable = false;
      this.worker?.postMessage({
        type: "audio-disabled",
        loadId: this.loadId,
      });
      this.#emit("warning", {
        message: `Web Audio is unavailable; playback will be silent. ${error.message}`,
      });
      return false;
    });
    return this.audioInitialization;
  }

  async #initializeAudio() {
    const AudioContext = window.AudioContext || window.webkitAudioContext;
    this.audioContext = new AudioContext({ latencyHint: "interactive" });
    this.audioContext.addEventListener("statechange", () => {
      if (
        this.audioContext.state !== "running" &&
        ["playing", "buffering", "draining"].includes(this.state)
      ) {
        this.pause();
        this.#emit("audiostate", {
          state: this.audioContext.state,
          message: "Playback paused because the audio device was interrupted.",
        });
      }
    });
    await this.audioContext.audioWorklet.addModule(
      new URL("./audio-worklet.js", import.meta.url),
    );

    this.audioNode = new AudioWorkletNode(
      this.audioContext,
      "mpeg-pcm-output",
      {
        numberOfInputs: 0,
        numberOfOutputs: 1,
        outputChannelCount: [2],
      },
    );
    this.gainNode = this.audioContext.createGain();
    this.audioNode.connect(this.gainNode).connect(this.audioContext.destination);
    this.#applyGain();

    const channel = new MessageChannel();
    this.audioNode.port.postMessage(
      { type: "attach", port: channel.port1 },
      [channel.port1],
    );
    this.worker.postMessage(
      { type: "audio-port", port: channel.port2 },
      [channel.port2],
    );
    return true;
  }

  #applyGain() {
    if (!this.gainNode || !this.audioContext) {
      return;
    }
    const gain = this.muted ? 0 : this.volume;
    this.gainNode.gain.setTargetAtTime(
      gain,
      this.audioContext.currentTime,
      0.015,
    );
  }

  async #cancelTransfer() {
    this.fetchAbortController?.abort();
    this.fetchAbortController = null;
    if (this.reader) {
      try {
        await this.reader.cancel();
      } catch {
        // A reader can already be closed while a replacement source is chosen.
      }
      this.reader = null;
    }

    if (this.loadId) {
      this.worker?.postMessage({ type: "cancel", loadId: this.loadId });
    }
    const cancellation = new DOMException("Media load replaced", "AbortError");
    for (const waiter of this.sourceWaiters.values()) {
      waiter.reject(cancellation);
    }
    this.sourceWaiters.clear();
    for (const waiter of this.chunkWaiters.values()) {
      waiter.reject(cancellation);
    }
    this.chunkWaiters.clear();
  }

  #receive(message) {
    switch (message?.type) {
      case "initialized":
        this.initializedWaiter?.resolve(message);
        this.initializedWaiter = null;
        break;

      case "source-ready": {
        const waiter = this.sourceWaiters.get(message.loadId);
        waiter?.resolve();
        this.sourceWaiters.delete(message.loadId);
        break;
      }

      case "chunk-consumed": {
        const key = `${message.loadId}:${message.chunkId}`;
        const waiter = this.chunkWaiters.get(key);
        waiter?.resolve();
        this.chunkWaiters.delete(key);
        break;
      }

      case "metadata":
        if (message.loadId === this.loadId) {
          this.metadata = message;
          if (message.duration > 0) {
            this.duration = message.duration;
          }
          this.#emit("metadata", message);
        }
        break;

      case "status":
        if (message.loadId === this.loadId) {
          this.state = message.state;
          this.currentTime = message.currentTime;
          if (message.duration > 0) {
            this.duration = message.duration;
          }
          this.#emit("status", {
            ...message,
            duration: this.duration,
          });
          this.#emit("statechange", { state: this.state });
        }
        break;

      case "ready":
        if (message.loadId === this.loadId) {
          if (this.state === "loading" || this.state === "buffering") {
            this.state = "ready";
          }
          this.#emit("ready", { loadId: message.loadId });
          this.#emit("statechange", { state: this.state });
        }
        break;

      case "ended":
        if (message.loadId === this.loadId) {
          this.state = "ended";
          this.#emit("ended", {});
          this.#emit("statechange", { state: this.state });
        }
        break;

      case "error":
        if (!message.loadId || message.loadId === this.loadId) {
          const error = new Error(message.message);
          this.sourceWaiters.get(message.loadId)?.reject(error);
          this.sourceWaiters.delete(message.loadId);
          for (const [key, waiter] of this.chunkWaiters) {
            if (key.startsWith(`${message.loadId}:`)) {
              waiter.reject(error);
              this.chunkWaiters.delete(key);
            }
          }
          this.state = "error";
          this.#emit("error", { message: message.message });
          this.#emit("statechange", { state: this.state });
        }
        break;

      default:
        break;
    }
  }

  #rejectPending(error) {
    this.initializedWaiter?.reject(error);
    for (const waiter of this.sourceWaiters.values()) {
      waiter.reject(error);
    }
    for (const waiter of this.chunkWaiters.values()) {
      waiter.reject(error);
    }
    this.sourceWaiters.clear();
    this.chunkWaiters.clear();
  }

  #emit(type, detail) {
    this.dispatchEvent(new CustomEvent(type, { detail }));
  }

  async destroy() {
    await this.#cancelTransfer();
    this.worker?.terminate();
    this.audioNode?.disconnect();
    this.gainNode?.disconnect();
    await this.audioContext?.close();
  }
}
