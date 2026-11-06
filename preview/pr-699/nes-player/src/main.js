import {
  filterRoms,
  listingUrl,
  parseListing,
  romUrl,
  sourceUrl,
} from "./catalog.js";
import {
  BUTTON,
  diffButtons,
  keyBinding,
  keyTable,
  padButtons,
} from "./controls.js";
import { Player } from "./player.js";
import { describeHeader, readHeader } from "./rom.js";

const CACHE_KEY = "nes-player.catalog";

const $ = (id) => document.getElementById(id);
const canvas = $("screen");
const statusEl = $("status");
const pauseBtn = $("pause");
const resetBtn = $("reset");
const muteBtn = $("mute");
const fullscreenBtn = $("fullscreen");
const fileInput = $("file");
const gamesEl = $("games");
const noteEl = $("library-note");
const searchEl = $("search");
const overlay = $("drop-overlay");

const player = new Player(canvas, {
  onError: (e) => {
    setStatus(`The emulator stopped: ${e.message}`, true);
    setRunning(false);
  },
});

let roms = [];
let current = "";

function setStatus(text, error = false) {
  statusEl.textContent = text;
  statusEl.classList.toggle("error", error);
}

function setRunning(running) {
  pauseBtn.disabled = !running;
  resetBtn.disabled = !running;
  fullscreenBtn.disabled = !running;
  pauseBtn.textContent = "Pause";
  $("screen-empty").hidden = running;
}

const SOUND_HINT = " Press a key or tap to turn on sound.";

function soundHint() {
  return player.audioBlocked ? SOUND_HINT : "";
}

function unlockAudio() {
  const blocked = player.audioBlocked;
  player.unlockAudio();
  if (blocked) statusEl.textContent = statusEl.textContent.replace(SOUND_HINT, "");
}

/**
 * @param {Uint8Array} bytes
 * @param {string} label
 */
function play(bytes, label) {
  let header;
  try {
    header = readHeader(bytes);
    player.load(bytes);
  } catch (e) {
    setStatus(`${label}: ${e.message}`, true);
    return false;
  }
  setRunning(true);
  setStatus(`${label}. ${describeHeader(header)}.${soundHint()}`);
  canvas.focus();
  return true;
}

async function playRepoRom(name) {
  player.unlockAudio();
  current = name;
  renderGames();
  setStatus(`Downloading ${name}.nes…`);
  let bytes;
  try {
    const res = await fetch(romUrl(name));
    if (!res.ok) throw new Error(`HTTP ${res.status}`);
    bytes = new Uint8Array(await res.arrayBuffer());
  } catch (e) {
    setStatus(`Couldn't download ${name}.nes: ${e.message}`, true);
    return;
  }
  if (current !== name) return;
  if (play(bytes, `${name}.nes`)) {
    const url = new URL(location.href);
    url.searchParams.set("rom", name);
    history.replaceState(null, "", url);
  }
}

async function playFile(file) {
  player.unlockAudio();
  current = "";
  renderGames();
  const bytes = new Uint8Array(await file.arrayBuffer());
  if (play(bytes, file.name)) {
    const url = new URL(location.href);
    url.searchParams.delete("rom");
    history.replaceState(null, "", url);
  }
}

function renderGames() {
  const shown = filterRoms(roms, searchEl.value);
  gamesEl.replaceChildren(
    ...shown.map((rom) => {
      const li = document.createElement("li");
      const btn = document.createElement("button");
      btn.type = "button";
      btn.className = "game";
      btn.textContent = rom.name;
      btn.setAttribute("aria-current", String(rom.name === current));
      btn.addEventListener("click", () => playRepoRom(rom.name));
      const src = document.createElement("a");
      src.href = sourceUrl(rom.name);
      src.className = "source";
      src.textContent = "Source";
      src.setAttribute("aria-label", `${rom.name}.ne source`);
      li.append(btn, src);
      return li;
    }),
  );
  if (roms.length && !shown.length) {
    noteEl.hidden = false;
    noteEl.textContent = "No games match.";
  } else if (roms.length) {
    noteEl.hidden = true;
  }
}

async function loadCatalog() {
  try {
    const res = await fetch(listingUrl(), {
      headers: { Accept: "application/vnd.github+json" },
    });
    if (!res.ok) throw new Error(`GitHub answered HTTP ${res.status}`);
    roms = parseListing(await res.json());
    try {
      localStorage.setItem(CACHE_KEY, JSON.stringify(roms));
    } catch {
      // Private browsing can refuse storage; the list still works.
    }
  } catch (e) {
    let cached = null;
    try {
      cached = JSON.parse(localStorage.getItem(CACHE_KEY) ?? "null");
    } catch {
      cached = null;
    }
    if (Array.isArray(cached) && cached.length) {
      roms = cached;
    } else {
      noteEl.textContent = `Couldn't load the list of games (${e.message}). You can still open a .nes file.`;
      noteEl.classList.add("error");
      return;
    }
  }
  if (!roms.length) {
    noteEl.textContent = "There are no ROMs on main.";
    return;
  }
  renderGames();
}

function renderKeys() {
  $("keys").replaceChildren(
    ...keyTable().map((cells) => {
      const tr = document.createElement("tr");
      cells.forEach((text, i) => {
        const cell = document.createElement(i === 0 ? "th" : "td");
        if (i === 0) cell.scope = "row";
        if (i > 0) {
          const kbd = document.createElement("kbd");
          kbd.textContent = text;
          cell.append(kbd);
        } else {
          cell.textContent = text;
        }
        tr.append(cell);
      });
      return tr;
    }),
  );
}

function typing(target) {
  return (
    target instanceof HTMLInputElement ||
    target instanceof HTMLTextAreaElement ||
    target instanceof HTMLSelectElement
  );
}

const keysDown = new Set();
document.addEventListener("keydown", (e) => {
  unlockAudio();
  if (typing(e.target)) return;
  const binding = keyBinding(e);
  if (!binding || !player.nes) return;
  e.preventDefault();
  if (e.repeat || keysDown.has(e.code)) return;
  keysDown.add(e.code);
  player.buttonDown(...binding);
});
document.addEventListener("keyup", (e) => {
  if (!keysDown.delete(e.code)) return;
  const binding = keyBinding(e) ?? null;
  if (binding) player.buttonUp(...binding);
});
window.addEventListener("blur", () => {
  for (const code of keysDown) {
    const binding = keyBinding({ code });
    if (binding) player.buttonUp(...binding);
  }
  keysDown.clear();
});
document.addEventListener("pointerdown", unlockAudio);

const padState = [new Set(), new Set()];
function pollGamepads() {
  const pads = navigator.getGamepads ? [...navigator.getGamepads()] : [];
  const connected = pads.filter(Boolean).slice(0, 2);
  for (let i = 0; i < 2; i++) {
    const held = connected[i] ? padButtons(connected[i]) : new Set();
    const { down, up } = diffButtons(padState[i], held);
    for (const b of down) player.buttonDown(i + 1, b);
    for (const b of up) player.buttonUp(i + 1, b);
    padState[i] = held;
  }
  requestAnimationFrame(pollGamepads);
}

for (const el of document.querySelectorAll("#pad [data-button]")) {
  const button = BUTTON[el.dataset.button];
  let held = false;
  const release = () => {
    if (!held) return;
    held = false;
    el.classList.remove("held");
    player.buttonUp(1, button);
  };
  el.addEventListener("pointerdown", (e) => {
    e.preventDefault();
    unlockAudio();
    el.setPointerCapture?.(e.pointerId);
    held = true;
    el.classList.add("held");
    player.buttonDown(1, button);
  });
  el.addEventListener("pointerup", release);
  el.addEventListener("pointercancel", release);
  el.addEventListener("lostpointercapture", release);
  el.addEventListener("contextmenu", (e) => e.preventDefault());
}

pauseBtn.addEventListener("click", () => {
  player.setPaused(!player.paused);
  pauseBtn.textContent = player.paused ? "Resume" : "Pause";
});
resetBtn.addEventListener("click", () => player.reset());
muteBtn.addEventListener("click", () => {
  player.setMuted(!player.muted);
  muteBtn.setAttribute("aria-pressed", String(player.muted));
  muteBtn.textContent = player.muted ? "Unmute" : "Mute";
});
fullscreenBtn.addEventListener("click", () => {
  canvas.parentElement.requestFullscreen?.().catch(() => {});
});
fileInput.addEventListener("change", () => {
  const [file] = fileInput.files;
  if (file) playFile(file);
  fileInput.value = "";
});
searchEl.addEventListener("input", renderGames);

let dragDepth = 0;
const hasFiles = (e) => [...(e.dataTransfer?.types ?? [])].includes("Files");
document.addEventListener("dragenter", (e) => {
  if (!hasFiles(e)) return;
  e.preventDefault();
  dragDepth++;
  overlay.hidden = false;
});
document.addEventListener("dragover", (e) => {
  if (!hasFiles(e)) return;
  e.preventDefault();
  e.dataTransfer.dropEffect = "copy";
});
document.addEventListener("dragleave", () => {
  dragDepth = Math.max(0, dragDepth - 1);
  if (!dragDepth) overlay.hidden = true;
});
document.addEventListener("drop", (e) => {
  if (!hasFiles(e)) return;
  e.preventDefault();
  dragDepth = 0;
  overlay.hidden = true;
  const [file] = e.dataTransfer.files;
  if (file) playFile(file);
});

renderKeys();
setRunning(false);
requestAnimationFrame(pollGamepads);
loadCatalog();
const wanted = new URLSearchParams(location.search).get("rom");
if (wanted && /^[\w.-]+$/.test(wanted)) playRepoRom(wanted);
