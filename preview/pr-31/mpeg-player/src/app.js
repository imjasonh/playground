import { formatBytes, formatTime, normalizeMediaUrl } from "./media.js";
import { MpegPlayerController } from "./player-controller.js";

const DOM_IDS = [
  "player-panel",
  "video-canvas",
  "drop-zone",
  "drop-prompt",
  "empty-state",
  "loading-overlay",
  "loading-label",
  "load-progress",
  "stage-state",
  "render-badge",
  "play-button",
  "seek-input",
  "current-time",
  "duration-time",
  "mute-button",
  "volume-input",
  "fullscreen-button",
  "status",
  "file-input",
  "demo-button",
  "side-demo-button",
  "url-form",
  "url-input",
  "source-name",
  "source-size",
  "decoder-value",
  "renderer-value",
  "video-value",
  "audio-value",
  "decode-value",
  "buffer-value",
];

const elements = Object.fromEntries(
  DOM_IDS.map((id) => [id, document.getElementById(id)]),
);
const controller = new MpegPlayerController(elements["video-canvas"]);
const demoUrl = new URL("../assets/demo.ts", import.meta.url).href;

let playable = false;
let scrubbing = false;
let dragDepth = 0;
let activeSource = { name: "", size: 0 };

function setStatus(message, error = false) {
  elements.status.textContent = message;
  elements.status.classList.toggle("is-error", error);
  elements.status.setAttribute("role", error ? "alert" : "status");
  elements.status.setAttribute("aria-live", error ? "assertive" : "polite");
}

function showError(message) {
  setLoading(false);
  setPlayable(false);
  elements["empty-state"].hidden = false;
  updatePlaybackState("error");
  setStatus(message, true);
}

function setLoading(loading) {
  elements["loading-overlay"].hidden = !loading;
  if (loading) {
    elements["empty-state"].hidden = true;
  }
}

function setSource(name, size = 0) {
  activeSource = { name, size };
  elements["source-name"].textContent = name;
  elements["source-size"].textContent = size ? formatBytes(size) : "stream";
}

function setPlayable(value) {
  playable = value;
  elements["play-button"].disabled = !value;
  elements["seek-input"].disabled = !value;
}

function updatePlaybackState(state) {
  const isPlaying = state === "playing";
  const isError = state === "error";
  const stateLabel =
    {
      idle: "idle",
      loading: "loading",
      ready: "ready",
      paused: "paused",
      playing: "playing",
      buffering: "buffering",
      draining: "finishing",
      ended: "ended",
      error: "error",
    }[state] || state;

  elements["stage-state"].querySelector("span").textContent = stateLabel;
  elements["stage-state"].classList.toggle("is-live", isPlaying);
  elements["stage-state"].classList.toggle("is-error", isError);
  elements["drop-zone"].classList.toggle("is-playing", isPlaying);
  elements["play-button"].querySelector("span").textContent = isPlaying ? "Ⅱ" : "▶";
  elements["play-button"].setAttribute("aria-label", isPlaying ? "Pause" : "Play");
}

function beginLoad(name, size = 0) {
  controller.pause();
  setSource(name, size);
  setPlayable(false);
  setLoading(true);
  elements["loading-label"].textContent = "Preparing WebAssembly decoder…";
  elements["load-progress"].style.width = "8%";
  elements["seek-input"].value = "0";
  elements["seek-input"].max = "0";
  elements["current-time"].textContent = "0:00";
  elements["duration-time"].textContent = "0:00";
  elements["video-value"].textContent = "—";
  elements["decode-value"].textContent = "—";
  elements["buffer-value"].textContent = "—";
  setStatus(`Opening ${name}…`);
}

async function runLoad(load) {
  try {
    await load();
  } catch (error) {
    if (error.name !== "AbortError") {
      showError(error.message);
    }
  }
}

async function loadFile(file) {
  if (!file) {
    return;
  }
  beginLoad(file.name, file.size);
  await runLoad(() => controller.loadFile(file));
  elements["file-input"].value = "";
}

async function loadDemo() {
  beginLoad("demo.ts");
  await runLoad(() => controller.loadUrl(demoUrl));
}

controller.addEventListener("capabilities", ({ detail }) => {
  elements["decoder-value"].textContent = detail.wasm
    ? "WebAssembly · worker"
    : "JavaScript · worker";
  elements["renderer-value"].textContent = detail.webgl
    ? "Offscreen WebGL"
    : "Offscreen Canvas 2D";
  elements["render-badge"].textContent = detail.webgl
    ? "offscreen webgl"
    : "offscreen canvas 2d";
  elements["audio-value"].textContent = detail.audio
    ? "AudioWorklet ready"
    : "Unavailable · silent";
  setStatus("Ready for an MPEG transport stream.");
});

controller.addEventListener("loadprogress", ({ detail }) => {
  const { loaded, total } = detail;
  if (total > 0) {
    const percent = Math.min(100, (loaded / total) * 100);
    elements["load-progress"].style.width = `${Math.max(8, percent)}%`;
    elements["loading-label"].textContent =
      percent >= 100 ? "Finalizing stream…" : `Loading · ${Math.round(percent)}%`;
  } else if (loaded > 0) {
    elements["load-progress"].style.width = "45%";
    elements["loading-label"].textContent = `Loading · ${formatBytes(loaded)}`;
  }
});

controller.addEventListener("metadata", ({ detail }) => {
  if (detail.name) {
    setSource(detail.name, detail.size || activeSource.size);
  }
  if (detail.width > 0 && detail.height > 0) {
    elements["drop-zone"].style.setProperty(
      "--video-aspect",
      `${detail.width} / ${detail.height}`,
    );
    const frameRate = detail.frameRate
      ? ` · ${detail.frameRate.toFixed(2).replace(/\.00$/, "")} fps`
      : "";
    elements["video-value"].textContent =
      `${detail.width}×${detail.height}${frameRate}`;
    setPlayable(true);
  }

  elements["decoder-value"].textContent = `${detail.decoder} · worker`;
  elements["renderer-value"].textContent = detail.renderer;
  elements["render-badge"].textContent = detail.renderer.toLowerCase();
  if (detail.hasAudio && detail.sampleRate) {
    elements["audio-value"].textContent =
      `${(detail.sampleRate / 1000).toFixed(1)} kHz · 2-channel output`;
  } else if (detail.hasAudio) {
    elements["audio-value"].textContent = "MP2 · starts on play";
  } else if (detail.hasAudio === false) {
    elements["audio-value"].textContent = "No MP2 track detected";
  }
});

controller.addEventListener("ready", () => {
  setLoading(false);
  setPlayable(true);
  elements["load-progress"].style.width = "100%";
  setStatus(`${activeSource.name} is ready. Press play.`);
});

controller.addEventListener("status", ({ detail }) => {
  if (!scrubbing) {
    elements["seek-input"].value = String(detail.currentTime);
    elements["current-time"].textContent = formatTime(detail.currentTime);
  }

  if (detail.duration > 0) {
    elements["seek-input"].max = String(detail.duration);
    elements["duration-time"].textContent = formatTime(detail.duration);
  }

  if (detail.decodeMilliseconds > 0) {
    const rate = detail.decodeFps > 0 ? ` · ${detail.decodeFps.toFixed(1)} fps` : "";
    elements["decode-value"].textContent =
      `${detail.decodeMilliseconds.toFixed(2)} ms/frame${rate}`;
  }
  if (
    detail.audioBufferedSeconds > 0 ||
    detail.audioUnderruns > 0 ||
    detail.audioDroppedFrames > 0
  ) {
    const underruns = detail.audioUnderruns
      ? ` · ${detail.audioUnderruns} underrun${detail.audioUnderruns === 1 ? "" : "s"}`
      : "";
    const dropped = detail.audioDroppedFrames
      ? ` · ${detail.audioDroppedFrames} dropped`
      : "";
    elements["buffer-value"].textContent =
      `${Math.round(detail.audioBufferedSeconds * 1000)} ms${underruns}${dropped}`;
  }

  if (detail.state === "buffering") {
    setStatus("Buffering media data…");
  }
});

controller.addEventListener("statechange", ({ detail }) => {
  updatePlaybackState(detail.state);
});

controller.addEventListener("ended", () => {
  setStatus("Playback finished.");
});

controller.addEventListener("warning", ({ detail }) => {
  elements["audio-value"].textContent = "Unavailable · silent";
  setStatus(detail.message);
});

controller.addEventListener("error", ({ detail }) => {
  showError(detail.message);
});

controller.addEventListener("audiostate", ({ detail }) => {
  setStatus(detail.message);
});

elements["file-input"].addEventListener("change", () => {
  loadFile(elements["file-input"].files[0]);
});
elements["demo-button"].addEventListener("click", loadDemo);
elements["side-demo-button"].addEventListener("click", loadDemo);

elements["url-form"].addEventListener("submit", (event) => {
  event.preventDefault();
  try {
    const url = normalizeMediaUrl(elements["url-input"].value);
    const name = decodeURIComponent(new URL(url).pathname.split("/").pop()) || "Remote stream";
    beginLoad(name);
    runLoad(() => controller.loadUrl(url));
  } catch (error) {
    showError(error.message);
    elements["url-input"].focus();
  }
});

elements["play-button"].addEventListener("click", async () => {
  if (!playable) {
    return;
  }
  if (controller.state === "playing") {
    controller.pause();
  } else {
    setStatus("Starting Web Audio and playback…");
    try {
      await controller.play();
      setStatus(`Playing ${activeSource.name}.`);
    } catch (error) {
      setStatus(error.message, true);
    }
  }
});

elements["video-canvas"].addEventListener("click", () => {
  elements["play-button"].click();
});

elements["seek-input"].addEventListener("input", () => {
  scrubbing = true;
  elements["current-time"].textContent = formatTime(
    Number(elements["seek-input"].value),
  );
});
elements["seek-input"].addEventListener("change", () => {
  controller.seek(Number(elements["seek-input"].value));
  scrubbing = false;
});

elements["volume-input"].addEventListener("input", () => {
  const volume = Number(elements["volume-input"].value);
  controller.setVolume(volume);
  if (volume > 0 && controller.muted) {
    controller.setMuted(false);
    elements["mute-button"].setAttribute("aria-pressed", "false");
  }
});

elements["mute-button"].addEventListener("click", () => {
  controller.setMuted(!controller.muted);
  elements["mute-button"].setAttribute("aria-pressed", String(controller.muted));
  elements["mute-button"].setAttribute(
    "aria-label",
    controller.muted ? "Unmute" : "Mute",
  );
  elements["mute-button"].querySelector("span").textContent = controller.muted
    ? "○"
    : "◕";
});

elements["fullscreen-button"].addEventListener("click", async () => {
  try {
    if (document.fullscreenElement) {
      await document.exitFullscreen();
    } else {
      await elements["player-panel"].requestFullscreen();
    }
  } catch {
    setStatus("Fullscreen is not available in this browser.", true);
  }
});

document.addEventListener("fullscreenchange", () => {
  const fullscreen = Boolean(document.fullscreenElement);
  elements["fullscreen-button"].setAttribute(
    "aria-label",
    fullscreen ? "Exit fullscreen" : "Enter fullscreen",
  );
});

for (const eventName of ["dragenter", "dragover"]) {
  elements["drop-zone"].addEventListener(eventName, (event) => {
    event.preventDefault();
    if (eventName === "dragenter") {
      dragDepth += 1;
    }
    elements["drop-zone"].classList.add("is-dragging");
    elements["drop-prompt"].hidden = false;
  });
}

elements["drop-zone"].addEventListener("dragleave", (event) => {
  event.preventDefault();
  dragDepth = Math.max(0, dragDepth - 1);
  if (dragDepth === 0) {
    elements["drop-zone"].classList.remove("is-dragging");
    elements["drop-prompt"].hidden = true;
  }
});

elements["drop-zone"].addEventListener("drop", (event) => {
  event.preventDefault();
  dragDepth = 0;
  elements["drop-zone"].classList.remove("is-dragging");
  elements["drop-prompt"].hidden = true;
  loadFile(event.dataTransfer?.files[0]);
});

window.addEventListener("keydown", (event) => {
  const interactive = event.target.closest("input, button, label");
  if (!playable || interactive) {
    return;
  }

  if (event.code === "Space") {
    event.preventDefault();
    elements["play-button"].click();
  } else if (event.code === "ArrowLeft" || event.code === "ArrowRight") {
    event.preventDefault();
    const direction = event.code === "ArrowLeft" ? -1 : 1;
    controller.seek(controller.currentTime + direction * 5);
  }
});

document.addEventListener("visibilitychange", () => {
  if (document.hidden && controller.state === "playing") {
    controller.pause();
  }
});

window.mpegCanvasPlayer = {
  controller,
  loadDemo,
  loadFile,
};

controller.init().then(() => {
  if (location.hash === "#demo") {
    loadDemo();
  }
}).catch((error) => {
  showError(error.message);
});
