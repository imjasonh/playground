import {
  DEFAULT_SENSITIVITY_DEG,
  DEFAULT_TOLERANCE_DEG,
  applyCalibration,
  axisOffsets,
  bubbleOffset,
  clamp,
  isLevel,
  tiltComponents,
} from "./level.js";

const SENSITIVITY = DEFAULT_SENSITIVITY_DEG;
const TOLERANCE = DEFAULT_TOLERANCE_DEG;
const SMOOTHING = 0.25;
const CALIBRATION_KEY = "bubble-level-calibration";

const enablePanel = document.querySelector("#enable-panel");
const enableBtn = document.querySelector("#enable-btn");
const enableText = document.querySelector("#enable-text");
const tiltValue = document.querySelector("#tilt-value");
const levelBadge = document.querySelector("#level-badge");
const axisXEl = document.querySelector("#axis-x");
const axisYEl = document.querySelector("#axis-y");
const bullseye = document.querySelector("#bullseye");
const bubble = document.querySelector("#bubble");
const tubeHBubble = document.querySelector("#tube-h-bubble");
const tubeVBubble = document.querySelector("#tube-v-bubble");
const calibrateBtn = document.querySelector("#calibrate-btn");
const resetBtn = document.querySelector("#reset-btn");
const statusEl = document.querySelector("#status");
const hintEl = document.querySelector("#hint");

const SENSOR_HINT =
  "Tip: rest the phone on the surface, then tap Calibrate to zero out any wobble.";
const PREVIEW_HINT =
  "Preview mode: drag inside the circle or use the arrow keys (press 0 to re-center). On a phone the real gyroscope drives the level.";

// Latest raw (uncalibrated) reading in degrees.
const raw = { beta: 0, gamma: 0 };
let calibration = loadCalibration();
let smoothBeta = 0;
let smoothGamma = 0;
let hasReading = false;
let sensorActive = false;
let previewMode = false;
let previewAttached = false;
let wasLevel = false;
let fallbackTimer = null;

function loadCalibration() {
  try {
    const stored = JSON.parse(localStorage.getItem(CALIBRATION_KEY));
    if (stored && Number.isFinite(stored.beta) && Number.isFinite(stored.gamma)) {
      return { beta: stored.beta, gamma: stored.gamma };
    }
  } catch {
    // Ignore malformed or unavailable storage.
  }
  return { beta: 0, gamma: 0 };
}

function saveCalibration() {
  try {
    localStorage.setItem(CALIBRATION_KEY, JSON.stringify(calibration));
  } catch {
    // Storage may be unavailable (private mode); calibration still works in memory.
  }
}

function isCalibrated() {
  return calibration.beta !== 0 || calibration.gamma !== 0;
}

function formatAxis(value, positiveWord, negativeWord) {
  const magnitude = Math.abs(value);
  if (magnitude < 0.05) {
    return "0.0°";
  }
  return `${magnitude.toFixed(1)}° ${value > 0 ? positiveWord : negativeWord}`;
}

function setSensorMode() {
  if (!sensorActive) {
    sensorActive = true;
  }
  previewMode = false;
  hasReading = true;
  hidePanel();
  if (fallbackTimer !== null) {
    clearTimeout(fallbackTimer);
    fallbackTimer = null;
  }
  statusEl.textContent = "";
  hintEl.textContent = SENSOR_HINT;
}

function hidePanel() {
  enablePanel.hidden = true;
}

function showPanel(message) {
  enableText.textContent = message;
  enablePanel.hidden = false;
}

function onOrientation(event) {
  if (event.beta === null && event.gamma === null) {
    // Some desktop browsers fire empty events; treat as "no sensor".
    return;
  }
  raw.beta = Number.isFinite(event.beta) ? event.beta : 0;
  raw.gamma = Number.isFinite(event.gamma) ? event.gamma : 0;
  if (!sensorActive) {
    setSensorMode();
  }
}

function startSensors() {
  window.addEventListener("deviceorientation", onOrientation);
  hintEl.textContent = SENSOR_HINT;
  // If no real reading arrives shortly, fall back to a pointer-driven preview
  // so the app is still usable on a laptop or a device without a gyroscope.
  fallbackTimer = setTimeout(() => {
    if (!sensorActive) {
      enablePreview("No motion sensor detected — drag the dial to preview.");
    }
  }, 1400);
}

function requestPermissionThenStart() {
  DeviceOrientationEvent.requestPermission()
    .then((state) => {
      if (state === "granted") {
        hidePanel();
        startSensors();
      } else {
        enablePreview("Motion access denied — drag the dial to preview.");
      }
    })
    .catch(() => {
      enablePreview("Motion access unavailable — drag the dial to preview.");
    });
}

function enablePreview(message) {
  if (sensorActive) {
    return;
  }
  previewMode = true;
  hasReading = true;
  hidePanel();
  statusEl.textContent = message;
  hintEl.textContent = PREVIEW_HINT;
  attachPreviewControls();
}

function attachPreviewControls() {
  if (previewAttached) {
    return;
  }
  previewAttached = true;

  const applyPointer = (clientX, clientY) => {
    const rect = bullseye.getBoundingClientRect();
    if (!rect.width || !rect.height) {
      return;
    }
    let x = clamp((clientX - (rect.left + rect.width / 2)) / (rect.width / 2), -1, 1);
    let y = clamp((clientY - (rect.top + rect.height / 2)) / (rect.height / 2), -1, 1);
    const magnitude = Math.hypot(x, y);
    if (magnitude > 1) {
      x /= magnitude;
      y /= magnitude;
    }
    // Invert the level mapping so the bubble tracks the pointer.
    raw.beta = clamp(-y * SENSITIVITY, -90, 90);
    raw.gamma = clamp(-x * SENSITIVITY, -90, 90);
  };

  let dragging = false;
  bullseye.addEventListener("pointerdown", (event) => {
    if (!previewMode) {
      return;
    }
    dragging = true;
    try {
      bullseye.setPointerCapture(event.pointerId);
    } catch {
      // Pointer capture is best-effort; dragging still works without it.
    }
    applyPointer(event.clientX, event.clientY);
    event.preventDefault();
  });
  bullseye.addEventListener("pointermove", (event) => {
    if (!dragging || !previewMode) {
      return;
    }
    applyPointer(event.clientX, event.clientY);
    event.preventDefault();
  });
  const endDrag = (event) => {
    if (!dragging) {
      return;
    }
    dragging = false;
    if (bullseye.hasPointerCapture?.(event.pointerId)) {
      bullseye.releasePointerCapture(event.pointerId);
    }
  };
  bullseye.addEventListener("pointerup", endDrag);
  bullseye.addEventListener("pointercancel", endDrag);

  window.addEventListener("keydown", (event) => {
    if (!previewMode) {
      return;
    }
    const step = 2;
    let handled = true;
    switch (event.key) {
      case "ArrowLeft":
        raw.gamma = clamp(raw.gamma + step, -90, 90);
        break;
      case "ArrowRight":
        raw.gamma = clamp(raw.gamma - step, -90, 90);
        break;
      case "ArrowUp":
        raw.beta = clamp(raw.beta + step, -90, 90);
        break;
      case "ArrowDown":
        raw.beta = clamp(raw.beta - step, -90, 90);
        break;
      case "0":
        raw.beta = 0;
        raw.gamma = 0;
        break;
      default:
        handled = false;
    }
    if (handled) {
      event.preventDefault();
    }
  });
}

function vibrate(pattern) {
  if (typeof navigator !== "undefined" && "vibrate" in navigator) {
    navigator.vibrate(pattern);
  }
}

// Degrees the screen is rotated from its natural orientation (0/90/180/270).
// DeviceOrientationEvent reports beta/gamma in the device's natural frame, so we
// use this to rotate the bubble back into the frame the user is looking at.
function getScreenAngle() {
  const orientation = window.screen && window.screen.orientation;
  if (orientation && typeof orientation.angle === "number") {
    return orientation.angle;
  }
  if (typeof window.orientation === "number") {
    return window.orientation;
  }
  return 0;
}

function render() {
  requestAnimationFrame(render);
  if (!hasReading) {
    return;
  }

  const adjusted = applyCalibration(raw, calibration);
  smoothBeta += (adjusted.beta - smoothBeta) * SMOOTHING;
  smoothGamma += (adjusted.gamma - smoothGamma) * SMOOTHING;

  const screenAngle = getScreenAngle();
  const offset = bubbleOffset(smoothBeta, smoothGamma, SENSITIVITY, screenAngle);
  const axes = axisOffsets(smoothBeta, smoothGamma, SENSITIVITY, screenAngle);
  const components = tiltComponents(smoothBeta, smoothGamma, screenAngle);
  const level = isLevel(smoothBeta, smoothGamma, TOLERANCE);

  bubble.style.setProperty("--bx", offset.x.toFixed(4));
  bubble.style.setProperty("--by", offset.y.toFixed(4));
  tubeHBubble.style.setProperty("--bx", axes.x.toFixed(4));
  tubeVBubble.style.setProperty("--by", axes.y.toFixed(4));

  tiltValue.textContent = components.total.toFixed(1);
  axisXEl.textContent = formatAxis(components.x, "right", "left");
  axisYEl.textContent = formatAxis(components.y, "back", "front");

  if (level) {
    levelBadge.textContent = "Level";
  } else {
    levelBadge.textContent = `Off by ${components.total.toFixed(1)}°`;
  }
  document.body.classList.toggle("is-level", level);

  if (level && !wasLevel) {
    vibrate(30);
  }
  wasLevel = level;
}

calibrateBtn.addEventListener("click", () => {
  if (!hasReading) {
    statusEl.textContent = "Waiting for the motion sensor…";
    return;
  }
  calibration = { beta: raw.beta, gamma: raw.gamma };
  saveCalibration();
  resetBtn.disabled = false;
  statusEl.textContent = "Calibrated — this surface now reads as level.";
});

resetBtn.addEventListener("click", () => {
  calibration = { beta: 0, gamma: 0 };
  try {
    localStorage.removeItem(CALIBRATION_KEY);
  } catch {
    // Ignore storage errors.
  }
  resetBtn.disabled = true;
  statusEl.textContent = "Calibration reset to factory zero.";
});

enableBtn.addEventListener("click", () => {
  if (
    typeof DeviceOrientationEvent !== "undefined" &&
    typeof DeviceOrientationEvent.requestPermission === "function"
  ) {
    requestPermissionThenStart();
  } else {
    startSensors();
  }
});

function init() {
  resetBtn.disabled = !isCalibrated();

  if (typeof DeviceOrientationEvent === "undefined") {
    enablePreview("Motion sensors aren't supported here — drag the dial to preview.");
  } else if (typeof DeviceOrientationEvent.requestPermission === "function") {
    // iOS Safari: a tap is required before the sensor can be read.
    showPanel("This level needs permission to use your device's motion sensors.");
  } else {
    startSensors();
  }

  requestAnimationFrame(render);
}

init();
