import { ESPLoader, Transport } from "../vendor/esptool-js.js";
import { DEFAULT_OTA_TAG, DEFAULT_PROXY_BASE, OTA_APP_INKBOT, OTA_APP_MAZE } from "./constants.js";
import { flashFirmware } from "./flash.js";
import { fetchFirmware } from "./ghcr.js";
import { formatBytes, inspectImage } from "./image.js";
import { getSerial, requestPort } from "./serial.js";

const STORAGE_PROXY = "esp-flash.proxyBase";

const el = {};

function $(id) {
  return document.getElementById(id);
}

function log(message, level = "info") {
  const line = document.createElement("div");
  line.className = `log-line log-${level}`;
  const time = new Date().toLocaleTimeString();
  line.textContent = `[${time}] ${message}`;
  el.log.appendChild(line);
  el.log.scrollTop = el.log.scrollHeight;
}

function setBadge(node, text, state) {
  node.textContent = text;
  node.dataset.state = state;
}

function selectedApp() {
  const value = document.querySelector('input[name="source"]:checked')?.value;
  if (value === OTA_APP_MAZE) {
    return OTA_APP_MAZE;
  }
  if (value === "file") {
    return "file";
  }
  return OTA_APP_INKBOT;
}

function proxyBase() {
  return (el.proxyBase.value || "").trim().replace(/\/+$/, "") || DEFAULT_PROXY_BASE;
}

function saveProxyBase() {
  try {
    localStorage.setItem(STORAGE_PROXY, proxyBase());
  } catch {
    // storage may be blocked
  }
}

let firmware = null;
let firmwareLabel = "";

function setFirmware(bytes, label) {
  const info = inspectImage(bytes);
  firmware = bytes;
  firmwareLabel = label;
  el.imageMeta.textContent = `${label}: ${formatBytes(info.size)}, ESP magic 0x${info.magic.toString(16)}, flash at 0x${info.flashAddress.toString(16)}`;
  el.flashBtn.disabled = false;
}

function clearFirmware() {
  firmware = null;
  firmwareLabel = "";
  el.imageMeta.textContent = "No image loaded.";
  el.flashBtn.disabled = true;
}

function setBusy(busy) {
  el.fetchBtn.disabled = busy;
  el.flashBtn.disabled = busy || !firmware;
  el.fileInput.disabled = busy;
  for (const input of document.querySelectorAll('input[name="source"]')) {
    input.disabled = busy;
  }
}

async function loadImage() {
  const source = selectedApp();
  if (source === "file") {
    const file = el.fileInput.files?.[0];
    if (!file) {
      clearFirmware();
      return;
    }
    const bytes = new Uint8Array(await file.arrayBuffer());
    setFirmware(bytes, file.name);
    return;
  }

  setBusy(true);
  el.progress.hidden = true;
  try {
    log(`Fetching ${source}:${DEFAULT_OTA_TAG} through the CORS proxy…`);
    const result = await fetchFirmware({
      app: source,
      proxyBase: proxyBase(),
    });
    setFirmware(result.bytes, `${source}@${result.digest.slice(0, 19)}`);
    log(`Loaded ${formatBytes(result.size)} (${result.digest}).`, "success");
  } catch (err) {
    clearFirmware();
    log(err.message || String(err), "error");
  } finally {
    setBusy(false);
  }
}

function terminal() {
  return {
    clean() {},
    writeLine(data) {
      log(String(data).trimEnd());
    },
    write(data) {
      const text = String(data);
      if (text.trim()) {
        log(text.trimEnd());
      }
    },
  };
}

async function flash() {
  if (!firmware) {
    log("Load a firmware image first.", "warn");
    return;
  }

  const { kind, serial } = await getSerial();
  if (kind === "none") {
    log("This browser has neither Web Serial nor WebUSB.", "error");
    return;
  }

  let port;
  try {
    port = await requestPort(serial);
  } catch (err) {
    if (err.name === "NotFoundError") {
      log("No serial port selected.", "warn");
      return;
    }
    log(err.message || String(err), "error");
    return;
  }

  const bothSlots = el.bothSlots.checked;
  setBusy(true);
  el.progress.hidden = false;
  el.progressBar.value = 0;
  el.progressLabel.textContent = "Connecting…";
  log(`Using ${kind}. Hold the device in download mode if connect fails (BOOT, then RESET).`);

  try {
    inspectImage(firmware);
    const result = await flashFirmware({
      port,
      firmware,
      bothSlots,
      ESPLoader,
      Transport,
      terminal: terminal(),
      onProgress(_fileIndex, written, total) {
        const pct = total ? Math.round((written / total) * 100) : 0;
        el.progressBar.value = pct;
        el.progressLabel.textContent = `${pct}% (${formatBytes(written)} / ${formatBytes(total)})`;
      },
    });
    el.progressBar.value = 100;
    el.progressLabel.textContent = "Done";
    log(`Wrote ${firmwareLabel} to ${result.chip}. The board is resetting.`, "success");
  } catch (err) {
    log(err.message || String(err), "error");
    el.progressLabel.textContent = "Failed";
  } finally {
    setBusy(false);
  }
}

async function describeBrowser() {
  const { kind } = await getSerial();
  if (kind === "web-serial") {
    setBadge(el.browserState, "Web Serial", "ok");
    el.browserHint.textContent =
      "Chrome or Edge on this computer will open a serial-port picker.";
    return;
  }
  if (kind === "webusb-polyfill") {
    setBadge(el.browserState, "WebUSB polyfill", "ok");
    el.browserHint.textContent =
      "This browser has WebUSB but not Web Serial. The page uses a polyfill so Android Chrome can flash too.";
    return;
  }
  setBadge(el.browserState, "unsupported", "bad");
  el.browserHint.textContent =
    "Use Chrome or Edge on desktop, or Chrome on Android. Safari and Firefox do not expose a serial or USB API a page can call.";
  el.flashBtn.disabled = true;
}

function sourceChanged() {
  const isFile = selectedApp() === "file";
  el.fileField.hidden = !isFile;
  el.fetchBtn.hidden = isFile;
  if (!isFile) {
    el.fileInput.value = "";
    clearFirmware();
  }
}

function cacheElements() {
  const ids = [
    "browser-state",
    "browser-hint",
    "proxy-base",
    "fetch-btn",
    "file-field",
    "file-input",
    "image-meta",
    "both-slots",
    "flash-btn",
    "progress",
    "progress-bar",
    "progress-label",
    "log",
    "clear-log-btn",
  ];
  for (const id of ids) {
    const camel = id.replace(/-([a-z])/g, (_m, c) => c.toUpperCase());
    el[camel] = $(id);
  }
}

async function init() {
  cacheElements();

  const params = new URLSearchParams(window.location.search);
  const fromQuery = (params.get("proxy") || "").trim();
  let stored = "";
  try {
    stored = localStorage.getItem(STORAGE_PROXY) || "";
  } catch {
    stored = "";
  }
  el.proxyBase.value = fromQuery || stored || DEFAULT_PROXY_BASE;

  await describeBrowser();
  sourceChanged();
  clearFirmware();

  document.querySelectorAll('input[name="source"]').forEach((input) => {
    input.addEventListener("change", sourceChanged);
  });
  el.fetchBtn.addEventListener("click", () => {
    saveProxyBase();
    loadImage();
  });
  el.fileInput.addEventListener("change", () => loadImage());
  el.flashBtn.addEventListener("click", () => flash());
  el.clearLogBtn.addEventListener("click", () => {
    el.log.textContent = "";
  });
  el.proxyBase.addEventListener("change", saveProxyBase);

  log("Load an image, then connect the ESP32 over USB and flash.");
}

if (document.readyState === "loading") {
  document.addEventListener("DOMContentLoaded", init);
} else {
  init();
}
