/* global JSMpeg */

// JSMpeg's compact distribution targets Window. These shims expose only the
// pieces needed by its decoder/renderer graph inside a dedicated worker.
self.window = self;
self.document = {
  readyState: "loading",
  addEventListener() {},
  querySelectorAll() {
    return [];
  },
  createElement() {
    return new OffscreenCanvas(1, 1);
  },
};
self.module = { exports: {} };
self.exports = self.module.exports;

if (typeof self.requestAnimationFrame !== "function") {
  self.requestAnimationFrame = (callback) =>
    setTimeout(() => callback(performance.now()), 16);
  self.cancelAnimationFrame = clearTimeout;
}

importScripts("../vendor/jsmpeg.min.js");

let canvas = null;
let player = null;
let activeLoadId = 0;
let audioPort = null;
let audioCapable = false;
let playbackState = "idle";
let mediaName = "";
let mediaSize = 0;
let mediaWidth = 0;
let mediaHeight = 0;
let audioBufferedSeconds = 0;
let audioUnderruns = 0;
let audioDroppedFrames = 0;
let decodedFrames = 0;
let measuredFrames = 0;
let measuredDecodeSeconds = 0;
let lastDecodeMilliseconds = 0;
let lastMeasurementAt = performance.now();
let webglSupported = null;
let reportedAudioSampleRate = 0;
let pauseReason = null;
let endTimer = null;

function send(message) {
  self.postMessage(message);
}

function sendError(message, loadId = activeLoadId) {
  send({ type: "error", loadId, message: String(message) });
}

function nowSeconds() {
  return performance.now() / 1000;
}

class PushSource {
  constructor(_url, options) {
    this.destination = null;
    this.streaming = false;
    this.completed = false;
    this.established = false;
    this.progress = 0;
    this.started = false;
    this.destroyed = false;
    this.loadId = options.loadId;
    this.onEstablishedCallback = options.onSourceEstablished;
    this.onCompletedCallback = options.onSourceCompleted;
  }

  connect(destination) {
    this.destination = destination;
  }

  start() {
    if (this.destroyed || this.loadId !== activeLoadId) {
      return;
    }
    this.started = true;
    send({ type: "source-ready", loadId: this.loadId });
  }

  push(buffer, loaded, total) {
    if (!this.started || this.destroyed || this.loadId !== activeLoadId) {
      return;
    }

    if (!this.established) {
      this.established = true;
      this.onEstablishedCallback?.(this);
    }
    this.progress = total > 0 ? loaded / total : 0;
    this.destination?.write(buffer);
  }

  finish() {
    if (this.destroyed || this.loadId !== activeLoadId) {
      return;
    }
    this.completed = true;
    this.progress = 1;
    this.onCompletedCallback?.(this);
  }

  resume() {}

  destroy() {
    this.destroyed = true;
  }
}

class WorkerAudioOutput {
  constructor(options) {
    this.generation = options.loadId;
    this.enabled = true;
    this.volume = 1;
    this.queueEnd = nowSeconds();
    this.stopped = false;
    this.draining = false;
    this.pausePosition = 0;
    this.sequence = 0;
    this.pendingDurations = new Map();
    Object.defineProperty(this, "enqueuedTime", {
      get: () => this.getEnqueuedTime(),
    });
    this.#resetRemote();
  }

  play(sampleRate, left, right) {
    if (!this.enabled) {
      return;
    }

    const now = nowSeconds();
    if (this.stopped) {
      this.hardReset();
      this.stopped = false;
    }

    const leftCopy = left.slice();
    const rightCopy = right.slice();
    const duration = leftCopy.length / sampleRate;
    const sequence = ++this.sequence;
    this.pendingDurations.set(sequence, duration);
    this.queueEnd = Math.max(this.queueEnd, now) + duration;

    audioPort?.postMessage(
      {
        type: "samples",
        generation: this.generation,
        sequence,
        sampleRate,
        left: leftCopy,
        right: rightCopy,
      },
      [leftCopy.buffer, rightCopy.buffer],
    );
  }

  stop() {
    this.pausePosition = currentTime();
    this.stopped = true;
    if (pauseReason === null && player?.source?.completed) {
      this.draining = true;
      return;
    }
    this.#resetRemote();
  }

  destroy() {
    this.hardReset();
  }

  resetEnqueuedTime() {
    this.hardReset();
  }

  hardReset() {
    this.queueEnd = nowSeconds();
    this.stopped = true;
    this.draining = false;
    this.pendingDurations.clear();
    this.#resetRemote();
  }

  reconcile(message) {
    if (
      this.stopped ||
      message.generation !== this.generation ||
      !Number.isFinite(message.bufferedSeconds)
    ) {
      return;
    }

    let pendingSeconds = 0;
    for (const [sequence, duration] of this.pendingDurations) {
      if (sequence <= message.sequence) {
        this.pendingDurations.delete(sequence);
      } else {
        pendingSeconds += duration;
      }
    }
    this.queueEnd =
      nowSeconds() + Math.max(0, message.bufferedSeconds) + pendingSeconds;
  }

  getEnqueuedTime() {
    return Math.max(this.queueEnd - nowSeconds(), 0);
  }

  #resetRemote() {
    audioPort?.postMessage({
      type: "reset",
      generation: this.generation,
    });
  }
}

WorkerAudioOutput.IsSupported = () => audioCapable;
JSMpeg.AudioOutput.WebAudio = WorkerAudioOutput;
JSMpeg.Renderer.WebGL.IsSupported = () => {
  if (webglSupported !== null) {
    return webglSupported;
  }
  try {
    const probe = new OffscreenCanvas(1, 1);
    const context = probe.getContext("webgl", {
      alpha: false,
      antialias: false,
      depth: false,
      stencil: false,
    });
    webglSupported = Boolean(context);
    context?.getExtension("WEBGL_lose_context")?.loseContext();
  } catch {
    webglSupported = false;
  }
  return webglSupported;
};

function resetMeasurements() {
  mediaWidth = 0;
  mediaHeight = 0;
  audioBufferedSeconds = 0;
  audioUnderruns = 0;
  audioDroppedFrames = 0;
  decodedFrames = 0;
  measuredFrames = 0;
  measuredDecodeSeconds = 0;
  lastDecodeMilliseconds = 0;
  lastMeasurementAt = performance.now();
  reportedAudioSampleRate = 0;
}

function rendererName() {
  if (!player?.renderer) {
    return "none";
  }
  return player.renderer.gl ? "Offscreen WebGL" : "Offscreen Canvas 2D";
}

function decoderName() {
  return player?.wasmModule ? "WebAssembly" : "JavaScript";
}

function startTime() {
  if (player?.audio?.canPlay) {
    return player.audio.startTime;
  }
  return player?.video?.startTime ?? 0;
}

function duration() {
  if (!player?.source?.completed) {
    return 0;
  }
  return Math.max(0, (player.demuxer?.currentTime ?? 0) - startTime());
}

function currentTime() {
  if (!player) {
    return 0;
  }
  const value = player.currentTime;
  return Number.isFinite(value) ? Math.max(0, value) : 0;
}

function sendMetadata() {
  send({
    type: "metadata",
    loadId: activeLoadId,
    name: mediaName,
    size: mediaSize,
    width: mediaWidth,
    height: mediaHeight,
    frameRate: player?.video?.frameRate ?? 0,
    sampleRate: player?.audio?.sampleRate ?? 0,
    hasAudio: Boolean(player?.audio?.canPlay),
    decoder: decoderName(),
    renderer: rendererName(),
    duration: duration(),
  });
}

function sendStatus() {
  if (!player) {
    return;
  }

  const now = performance.now();
  const elapsed = Math.max((now - lastMeasurementAt) / 1000, 0.001);
  const decodeFps = measuredFrames / elapsed;
  if (measuredFrames > 0) {
    lastDecodeMilliseconds =
      (measuredDecodeSeconds / measuredFrames) * 1000;
  }
  measuredFrames = 0;
  measuredDecodeSeconds = 0;
  lastMeasurementAt = now;

  send({
    type: "status",
    loadId: activeLoadId,
    state: playbackState,
    currentTime: currentTime(),
    duration: duration(),
    decodedFrames,
    decodeFps,
    decodeMilliseconds: lastDecodeMilliseconds,
    audioBufferedSeconds,
    audioUnderruns,
    audioDroppedFrames,
  });
}

function destroyPlayer() {
  if (!player) {
    return;
  }
  clearTimeout(endTimer);
  endTimer = null;
  try {
    pauseReason = "destroy";
    player.destroy();
  } catch (error) {
    console.warn("Failed to destroy MPEG player", error);
  } finally {
    pauseReason = null;
  }
  player = null;
}

function createPlayer(message) {
  destroyPlayer();
  activeLoadId = message.loadId;
  mediaName = message.name || "MPEG stream";
  mediaSize = Number(message.size) || 0;
  playbackState = "loading";
  resetMeasurements();

  try {
    player = new JSMpeg.Player("", {
      source: PushSource,
      canvas,
      loadId: activeLoadId,
      autoplay: false,
      loop: false,
      pauseWhenHidden: false,
      preserveDrawingBuffer: false,
      decodeFirstFrame: true,
      audio: audioCapable,
      onVideoDecode(_decoder, elapsedSeconds) {
        decodedFrames += 1;
        measuredFrames += 1;
        measuredDecodeSeconds += elapsedSeconds;
        if (playbackState === "buffering" && !player.paused) {
          playbackState = "playing";
        }
      },
      onAudioDecode(decoder) {
        if (
          decoder.sampleRate > 0 &&
          decoder.sampleRate !== reportedAudioSampleRate
        ) {
          reportedAudioSampleRate = decoder.sampleRate;
          sendMetadata();
        }
      },
      onPlay() {
        clearTimeout(endTimer);
        endTimer = null;
        playbackState = "playing";
        sendStatus();
      },
      onPause() {
        const output = player?.audioOut;
        if (output?.draining) {
          playbackState = "draining";
          sendStatus();
          return;
        }

        const pausePosition = output?.pausePosition;
        output?.hardReset();
        if (Number.isFinite(pausePosition)) {
          player.seek(pausePosition);
        }
        playbackState = "paused";
        sendStatus();
      },
      onEnded() {
        const loadId = activeLoadId;
        const remaining = player?.audioOut?.draining
          ? player.audioOut.getEnqueuedTime()
          : 0;
        const finish = () => {
          if (loadId !== activeLoadId || !player) {
            return;
          }
          player.audioOut?.hardReset();
          playbackState = "ended";
          send({ type: "ended", loadId });
          sendStatus();
        };

        if (remaining > 0.01) {
          playbackState = "draining";
          sendStatus();
          endTimer = setTimeout(finish, (remaining + 0.02) * 1000);
        } else {
          finish();
        }
      },
      onStalled() {
        if (!player?.source?.completed) {
          playbackState = "buffering";
          sendStatus();
        }
      },
    });

    const originalResize = player.renderer?.resize.bind(player.renderer);
    if (originalResize) {
      player.renderer.resize = (width, height) => {
        originalResize(width, height);
        mediaWidth = width;
        mediaHeight = height;
        sendMetadata();
      };
    }
    sendStatus();
  } catch (error) {
    destroyPlayer();
    sendError(error?.message || error, message.loadId);
  }
}

function attachAudioPort(port) {
  audioPort?.close();
  audioPort = port;
  audioPort.onmessage = ({ data }) => {
    if (
      data?.type !== "telemetry" ||
      data.generation !== activeLoadId
    ) {
      return;
    }
    audioBufferedSeconds = Number(data.bufferedSeconds) || 0;
    audioUnderruns = Number(data.underruns) || 0;
    audioDroppedFrames = Number(data.droppedFrames) || 0;
    player?.audioOut?.reconcile(data);
  };
  audioPort.start();

  if (activeLoadId) {
    audioPort.postMessage({
      type: "reset",
      generation: activeLoadId,
    });
  }
}

function pausePlayer(reason) {
  pauseReason = reason;
  try {
    player.pause();
  } finally {
    pauseReason = null;
  }
}

function seek(time) {
  if (!player) {
    return;
  }

  const target = Math.max(0, Math.min(Number(time) || 0, duration() || Infinity));
  const shouldResume = !player.paused;
  if (shouldResume) {
    pausePlayer("seek");
  } else {
    player.audioOut?.hardReset();
  }
  player.seek(target);
  if (player.video?.canPlay) {
    player.video.decode();
  }
  playbackState = shouldResume ? "playing" : "paused";
  if (shouldResume) {
    player.play();
  }
  sendStatus();
}

self.onmessage = ({ data: message }) => {
  try {
    switch (message?.type) {
      case "init":
        canvas = message.canvas;
        audioCapable = Boolean(message.audioCapable);
        WorkerAudioOutput.IsSupported = () => audioCapable;
        send({
          type: "initialized",
          wasm: typeof WebAssembly === "object",
          webgl: JSMpeg.Renderer.WebGL.IsSupported(),
        });
        break;

      case "audio-port":
        attachAudioPort(message.port);
        break;

      case "load":
        if (!canvas) {
          throw new Error("The OffscreenCanvas is not initialized.");
        }
        createPlayer(message);
        break;

      case "chunk":
        if (message.loadId === activeLoadId && player?.source) {
          player.source.push(message.buffer, message.loaded, message.total);
        }
        send({
          type: "chunk-consumed",
          loadId: message.loadId,
          chunkId: message.chunkId,
        });
        break;

      case "complete":
        if (message.loadId === activeLoadId && player?.source) {
          player.source.finish();
          if (mediaWidth === 0 || mediaHeight === 0) {
            playbackState = "error";
            sendError(
              "No MPEG-1 video track was found. Convert the source to MPEG-TS with MPEG-1 video.",
            );
            break;
          }
          playbackState = player.paused ? "ready" : "playing";
          sendMetadata();
          send({ type: "ready", loadId: activeLoadId });
          sendStatus();
        }
        break;

      case "play":
        if (player && message.loadId === activeLoadId) {
          if (playbackState === "ended" || playbackState === "draining") {
            clearTimeout(endTimer);
            endTimer = null;
            player.audioOut?.hardReset();
            seek(0);
          }
          playbackState = "playing";
          player.play();
          sendStatus();
        }
        break;

      case "pause":
        if (
          player &&
          message.loadId === activeLoadId &&
          !player.paused
        ) {
          pausePlayer("user");
        }
        break;

      case "seek":
        if (message.loadId === activeLoadId) {
          seek(message.time);
        }
        break;

      case "cancel":
        if (message.loadId === activeLoadId) {
          destroyPlayer();
          playbackState = "idle";
        }
        break;

      default:
        break;
    }
  } catch (error) {
    sendError(error?.message || error, message?.loadId);
  }
};

setInterval(sendStatus, 250);
