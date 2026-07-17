import { CHANNELS, CHANNEL_LABELS, DUTY_LABELS } from "./apu/constants.js";
import { formatNoteName } from "./apu/notes.js";
import { AudioEngine } from "./audio/engine.js";
import { songToWavBlob } from "./export/wav.js";
import { createKeyboardInput } from "./input/keyboard.js";
import { createMidiInput, isMidiSupported } from "./input/midi.js";
import {
  clearStep,
  overdubNote,
  patternToJSON,
  resizePattern,
} from "./sequencer/pattern.js";
import {
  createDemoSong,
  createSong,
  serializeSong,
  deserializeSong,
  songToJSON,
} from "./song.js";

const STORAGE_KEY = "nes-seq-song-v1";

/** @type {import("./song.js").Song} */
let song = loadSong();
/** @type {import("./instruments/macros.js").ChannelId} */
let selectedChannel = "pulse1";
let selectedStep = 0;
let playheadStep = 0;
let octaveBase = 48; // C3
let audioReady = false;
let playing = false;
let recording = false;

const engine = new AudioEngine();

const els = {
  play: document.getElementById("btn-play"),
  stop: document.getElementById("btn-stop"),
  record: document.getElementById("btn-record"),
  bpm: document.getElementById("input-bpm"),
  length: document.getElementById("select-length"),
  demo: document.getElementById("btn-demo"),
  clear: document.getElementById("btn-clear"),
  exportBtn: document.getElementById("btn-export"),
  midiBtn: document.getElementById("btn-midi"),
  channelList: document.getElementById("channel-list"),
  stepGrid: document.getElementById("step-grid"),
  statusAudio: document.getElementById("status-audio"),
  statusMidi: document.getElementById("status-midi"),
  statusStep: document.getElementById("status-step"),
  instName: document.getElementById("inst-name"),
  instDuty: document.getElementById("inst-duty"),
  instVolume: document.getElementById("inst-volume"),
  instVolumeOut: document.getElementById("inst-volume-out"),
  instArp: document.getElementById("inst-arp"),
  instSpeed: document.getElementById("inst-speed"),
  instShortNoise: document.getElementById("inst-short-noise"),
  instNoiseWrap: document.getElementById("inst-noise-wrap"),
  octDown: document.getElementById("btn-oct-down"),
  octUp: document.getElementById("btn-oct-up"),
  octaveLabel: document.getElementById("octave-label"),
};

function loadSong() {
  try {
    const raw = localStorage.getItem(STORAGE_KEY);
    if (raw) return deserializeSong(raw);
  } catch {
    /* ignore */
  }
  return createDemoSong();
}

function persist() {
  try {
    localStorage.setItem(STORAGE_KEY, serializeSong(song));
  } catch {
    /* ignore quota */
  }
}

function syncEngineSong() {
  if (!audioReady) return;
  engine.setBpm(song.bpm);
  engine.setPattern(patternToJSON(song.pattern));
  engine.setInstruments(song.instruments);
}

async function ensureAudio() {
  if (audioReady) {
    await engine.resume();
    return;
  }
  els.statusAudio.textContent = "Audio: starting…";
  await engine.init({
    pattern: patternToJSON(song.pattern),
    instruments: song.instruments,
    bpm: song.bpm,
  });
  engine.onTransport = (state) => {
    playheadStep = state.step;
    playing = state.playing;
    recording = state.recording;
    updateTransportUi();
    highlightPlayhead();
  };
  audioReady = true;
  els.statusAudio.textContent = `Audio: ${engine.mode === "worklet" ? "APU worklet" : "fallback"} · 44.1 kHz`;
}

function updateTransportUi() {
  els.play.setAttribute("aria-pressed", playing ? "true" : "false");
  els.play.classList.toggle("is-active", playing);
  els.play.textContent = playing ? "Playing" : "Play";
  els.record.setAttribute("aria-pressed", recording ? "true" : "false");
  els.statusStep.innerHTML = `Step <strong>${String(playheadStep + 1).padStart(2, "0")}</strong>`;
}

function renderChannels() {
  els.channelList.innerHTML = "";
  for (const ch of CHANNELS) {
    const btn = document.createElement("button");
    btn.type = "button";
    btn.className = "btn channel";
    btn.dataset.channel = ch;
    btn.setAttribute("aria-pressed", ch === selectedChannel ? "true" : "false");
    const inst = song.instruments[ch];
    btn.innerHTML = `<span>${CHANNEL_LABELS[ch]}</span><span>${inst.name}</span>`;
    btn.addEventListener("click", () => {
      selectedChannel = ch;
      renderChannels();
      renderInstrument();
      renderGrid();
    });
    els.channelList.appendChild(btn);
  }
}

function renderInstrument() {
  const inst = song.instruments[selectedChannel];
  els.instName.value = inst.name;
  els.instDuty.value = String(inst.duty);
  els.instVolume.value = String(inst.volume);
  els.instVolumeOut.textContent = String(inst.volume);
  els.instArp.value = inst.arpMacro.join(" ");
  els.instSpeed.value = String(inst.macroSpeed);
  els.instShortNoise.checked = inst.shortNoise;
  const isPulse = selectedChannel === "pulse1" || selectedChannel === "pulse2";
  const isNoise = selectedChannel === "noise";
  els.instDuty.disabled = !isPulse;
  els.instNoiseWrap.hidden = !isNoise;
  els.instDuty.title = isPulse
    ? DUTY_LABELS[inst.duty]
    : "Duty applies to pulse channels only";
}

function parseArp(text) {
  if (!text.trim()) return [];
  return text
    .trim()
    .split(/[\s,]+/)
    .map((n) => Number(n))
    .filter((n) => Number.isFinite(n))
    .map((n) => Math.max(-24, Math.min(24, n | 0)))
    .slice(0, 16);
}

function applyInstrumentFromForm() {
  const inst = song.instruments[selectedChannel];
  inst.name = els.instName.value.trim() || inst.name;
  inst.duty = Number(els.instDuty.value) | 0;
  inst.volume = Number(els.instVolume.value) | 0;
  inst.arpMacro = parseArp(els.instArp.value);
  inst.macroSpeed = Math.max(1, Number(els.instSpeed.value) | 0);
  inst.shortNoise = els.instShortNoise.checked;
  els.instVolumeOut.textContent = String(inst.volume);
  persist();
  syncEngineSong();
  renderChannels();
}

function renderGrid() {
  const len = song.pattern.length;
  els.stepGrid.style.setProperty("--steps", String(len));
  els.stepGrid.innerHTML = "";

  const header = document.createElement("div");
  header.className = "step-header";
  header.style.setProperty("--steps", String(len));
  header.innerHTML =
    `<span></span>` +
    Array.from({ length: len }, (_, i) => `<span>${i + 1}</span>`).join("");
  els.stepGrid.appendChild(header);

  for (const ch of CHANNELS) {
    const row = document.createElement("div");
    row.className = "step-row";
    row.dataset.channel = ch;
    row.style.setProperty("--steps", String(len));
    row.setAttribute("role", "row");

    const label = document.createElement("div");
    label.className = "step-label";
    label.textContent = CHANNEL_LABELS[ch];
    row.appendChild(label);

    for (let i = 0; i < len; i += 1) {
      const cell = document.createElement("button");
      cell.type = "button";
      cell.className = "step-cell";
      cell.dataset.channel = ch;
      cell.dataset.step = String(i);
      cell.setAttribute("role", "gridcell");
      const note = song.pattern.tracks[ch][i];
      if (note) {
        cell.classList.add("has-note");
        cell.textContent = formatNoteName(note.midi);
        cell.title = `${formatNoteName(note.midi)} · vel ${note.velocity ?? "—"}`;
      } else {
        cell.textContent = "";
        cell.title = `Step ${i + 1}`;
      }
      if (i === selectedStep && ch === selectedChannel) {
        cell.classList.add("is-selected");
      }
      if (playing && i === playheadStep) {
        cell.classList.add("is-playhead");
      }
      cell.addEventListener("click", () => onCellClick(ch, i));
      cell.addEventListener("contextmenu", (event) => {
        event.preventDefault();
        song.pattern = clearStep(song.pattern, ch, i);
        persist();
        syncEngineSong();
        renderGrid();
      });
      row.appendChild(cell);
    }
    els.stepGrid.appendChild(row);
  }
}

function highlightPlayhead() {
  for (const cell of els.stepGrid.querySelectorAll(".step-cell")) {
    const step = Number(cell.dataset.step);
    cell.classList.toggle("is-playhead", playing && step === playheadStep);
  }
  els.statusStep.innerHTML = `Step <strong>${String(playheadStep + 1).padStart(2, "0")}</strong>`;
}

/**
 * @param {import("./instruments/macros.js").ChannelId} channel
 * @param {number} step
 */
function onCellClick(channel, step) {
  selectedChannel = channel;
  selectedStep = step;
  renderChannels();
  renderInstrument();
  renderGrid();
}

/**
 * @param {number} midi
 * @param {number} [velocity]
 */
function handleNoteOn(midi, velocity = 12) {
  const ch = selectedChannel;
  engine.noteOn(ch, midi, velocity);

  if (recording && playing) {
    const step = playheadStep;
    song.pattern = overdubNote(song.pattern, ch, step, midi, {
      velocity,
      length: 1,
    });
    persist();
    syncEngineSong();
    renderGrid();
  } else if (!playing) {
    // Step entry mode: write into selected cell.
    song.pattern = overdubNote(song.pattern, ch, selectedStep, midi, {
      velocity,
      length: 1,
    });
    selectedStep = (selectedStep + 1) % song.pattern.length;
    persist();
    syncEngineSong();
    renderGrid();
  }
}

/**
 * @param {number} _midi
 */
function handleNoteOff(_midi) {
  engine.noteOff(selectedChannel);
}

function updateOctaveLabel() {
  els.octaveLabel.textContent = formatNoteName(octaveBase);
}

const keyboard = createKeyboardInput({
  getBaseMidi: () => octaveBase,
  onNoteOn: (midi) => handleNoteOn(midi, 12),
  onNoteOff: handleNoteOff,
  shouldIgnore: () => {
    const tag = document.activeElement?.tagName;
    return tag === "INPUT" || tag === "SELECT" || tag === "TEXTAREA";
  },
});

const midi = createMidiInput({
  onNoteOn: (m, v) => handleNoteOn(m, v),
  onNoteOff: handleNoteOff,
  onStatus: (info) => {
    if (!info.supported) {
      els.statusMidi.textContent = "MIDI: unsupported (use Chrome/Firefox)";
      els.midiBtn.disabled = true;
      return;
    }
    if (info.error) {
      els.statusMidi.textContent = `MIDI: ${info.error}`;
      return;
    }
    els.statusMidi.textContent = info.connected
      ? `MIDI: ${info.name || "connected"}`
      : "MIDI: enabled — plug in a controller";
  },
});

els.play.addEventListener("click", async () => {
  await ensureAudio();
  engine.play();
  playing = true;
  updateTransportUi();
});

els.stop.addEventListener("click", async () => {
  await ensureAudio();
  engine.stop();
  playing = false;
  recording = false;
  playheadStep = 0;
  updateTransportUi();
  highlightPlayhead();
});

els.record.addEventListener("click", async () => {
  await ensureAudio();
  recording = !recording;
  engine.setRecording(recording);
  if (recording) playing = true;
  updateTransportUi();
});

els.bpm.addEventListener("change", () => {
  const bpm = Math.max(40, Math.min(280, Number(els.bpm.value) || 120));
  els.bpm.value = String(bpm);
  song.bpm = bpm;
  persist();
  syncEngineSong();
});

els.length.addEventListener("change", () => {
  const length = Number(els.length.value) || 16;
  song.pattern = resizePattern(song.pattern, length);
  if (selectedStep >= song.pattern.length) selectedStep = 0;
  persist();
  syncEngineSong();
  renderGrid();
});

els.demo.addEventListener("click", () => {
  song = createDemoSong();
  els.bpm.value = String(song.bpm);
  els.length.value = String(song.pattern.length);
  persist();
  syncEngineSong();
  renderChannels();
  renderInstrument();
  renderGrid();
});

els.clear.addEventListener("click", () => {
  song = createSong({
    title: "Untitled",
    bpm: song.bpm,
    length: song.pattern.length,
  });
  persist();
  syncEngineSong();
  renderChannels();
  renderInstrument();
  renderGrid();
});

els.exportBtn.addEventListener("click", async () => {
  els.exportBtn.disabled = true;
  els.exportBtn.textContent = "Rendering…";
  try {
    // Yield so the label paints before the synchronous render.
    await new Promise((r) => setTimeout(r, 20));
    const blob = songToWavBlob(song, { loops: 2, sampleRate: 44100 });
    const url = URL.createObjectURL(blob);
    const a = document.createElement("a");
    a.href = url;
    a.download = `${slugify(song.title) || "nes-seq"}.wav`;
    a.click();
    URL.revokeObjectURL(url);
  } finally {
    els.exportBtn.disabled = false;
    els.exportBtn.textContent = "Export WAV";
  }
});

els.midiBtn.addEventListener("click", async () => {
  await midi.start();
});

els.octDown.addEventListener("click", () => {
  octaveBase = Math.max(24, octaveBase - 12);
  updateOctaveLabel();
});
els.octUp.addEventListener("click", () => {
  octaveBase = Math.min(96, octaveBase + 12);
  updateOctaveLabel();
});

for (const el of [
  els.instName,
  els.instDuty,
  els.instVolume,
  els.instArp,
  els.instSpeed,
  els.instShortNoise,
]) {
  el.addEventListener("change", applyInstrumentFromForm);
  el.addEventListener("input", () => {
    if (el === els.instVolume) {
      els.instVolumeOut.textContent = els.instVolume.value;
    }
  });
}

function slugify(text) {
  return String(text)
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, "-")
    .replace(/(^-|-$)/g, "");
}

function boot() {
  els.bpm.value = String(song.bpm);
  els.length.value = String(song.pattern.length);
  if (!isMidiSupported()) {
    els.statusMidi.textContent = "MIDI: unsupported (use Chrome/Firefox)";
    els.midiBtn.disabled = true;
  }
  renderChannels();
  renderInstrument();
  renderGrid();
  updateOctaveLabel();
  updateTransportUi();
  keyboard.attach();

  // Expose for debugging / tests in the page.
  window.__nesSeq = {
    getSong: () => songToJSON(song),
    engine,
  };
}

boot();
