import { CHANNELS, CHANNEL_LABELS, DUTY_LABELS } from "./apu/constants.js";
import { formatNoteName } from "./apu/notes.js";
import { AudioEngine } from "./audio/engine.js";
import { songToNsfBlob } from "./export/nsf.js";
import { songToWavBlob } from "./export/wav.js";
import { createKeyboardInput } from "./input/keyboard.js";
import { createMidiInput, isMidiSupported } from "./input/midi.js";
import {
  cloneInstrument,
  createDefaultInstruments,
  presetsForChannel,
} from "./instruments/macros.js";
import {
  clearStep,
  getStep,
  overdubNote,
  patternToJSON,
  resizePattern,
  setCut,
  setStep,
} from "./sequencer/pattern.js";
import { TICKS_PER_STEP } from "./sequencer/transport.js";
import {
  addPattern,
  appendOrder,
  createDemoSong,
  createSong,
  deletePattern,
  deserializeSong,
  duplicateEditPattern,
  getEditPattern,
  removeOrderEntry,
  selectEditPattern,
  serializeSong,
  setEditPatternData,
  setOrder,
  songToJSON,
} from "./song.js";

const STORAGE_KEY = "nes-seq-song-v2";

/** @type {import("./song.js").Song} */
let song = loadSong();
/** @type {import("./instruments/macros.js").ChannelId} */
let selectedChannel = "pulse1";
let selectedStep = 0;
let playheadStep = 0;
let playheadOrder = 0;
let octaveBase = 48;
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
  exportNsfBtn: document.getElementById("btn-export-nsf"),
  midiBtn: document.getElementById("btn-midi"),
  channelList: document.getElementById("channel-list"),
  stepGrid: document.getElementById("step-grid"),
  statusAudio: document.getElementById("status-audio"),
  statusMidi: document.getElementById("status-midi"),
  statusStep: document.getElementById("status-step"),
  instPreset: document.getElementById("inst-preset"),
  instName: document.getElementById("inst-name"),
  instDuty: document.getElementById("inst-duty"),
  instVolume: document.getElementById("inst-volume"),
  instVolumeOut: document.getElementById("inst-volume-out"),
  instArp: document.getElementById("inst-arp"),
  instPitch: document.getElementById("inst-pitch"),
  instVibSpeed: document.getElementById("inst-vib-speed"),
  instVibDepth: document.getElementById("inst-vib-depth"),
  instDelay: document.getElementById("inst-delay"),
  instSpeed: document.getElementById("inst-speed"),
  instShortNoise: document.getElementById("inst-short-noise"),
  instNoiseWrap: document.getElementById("inst-noise-wrap"),
  octDown: document.getElementById("btn-oct-down"),
  octUp: document.getElementById("btn-oct-up"),
  octaveLabel: document.getElementById("octave-label"),
  patternTabs: document.getElementById("pattern-tabs"),
  orderList: document.getElementById("order-list"),
  patAdd: document.getElementById("btn-pat-add"),
  patDup: document.getElementById("btn-pat-dup"),
  patDel: document.getElementById("btn-pat-del"),
  orderAdd: document.getElementById("btn-order-add"),
  noteInspector: document.getElementById("note-inspector"),
  noteLength: document.getElementById("note-length"),
  noteGate: document.getElementById("note-gate"),
  noteSlide: document.getElementById("note-slide"),
  noteCut: document.getElementById("btn-note-cut"),
};

function loadSong() {
  try {
    const raw =
      localStorage.getItem(STORAGE_KEY) ||
      localStorage.getItem("nes-seq-song-v1");
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
    /* ignore */
  }
}

function editPattern() {
  return getEditPattern(song);
}

function syncEngineSong() {
  if (!audioReady) return;
  engine.setBpm(song.bpm);
  engine.setSong({
    patterns: song.patterns.map(patternToJSON),
    order: song.order,
  });
  engine.setInstruments(song.instruments);
}

async function ensureAudio() {
  if (audioReady) {
    await engine.resume();
    return;
  }
  els.statusAudio.textContent = "Audio: starting…";
  await engine.init({
    patterns: song.patterns.map(patternToJSON),
    order: song.order,
    instruments: song.instruments,
    bpm: song.bpm,
  });
  engine.onTransport = (state) => {
    playheadStep = state.step;
    playheadOrder = state.orderIndex ?? 0;
    playing = state.playing;
    recording = state.recording;
    updateTransportUi();
    highlightPlayhead();
    renderOrder();
  };
  audioReady = true;
  els.statusAudio.textContent = `Audio: ${engine.mode === "worklet" ? "APU worklet" : "fallback"} · 44.1 kHz`;
}

function updateTransportUi() {
  els.play.setAttribute("aria-pressed", playing ? "true" : "false");
  els.play.classList.toggle("is-active", playing);
  els.play.textContent = playing ? "Playing" : "Play";
  els.record.setAttribute("aria-pressed", recording ? "true" : "false");
  const ord = song.order[playheadOrder] ?? 0;
  const name = song.patterns[ord]?.name || String.fromCharCode(65 + ord);
  els.statusStep.innerHTML = `Pat <strong>${name}</strong> · Step <strong>${String(playheadStep + 1).padStart(2, "0")}</strong>`;
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
      renderNoteInspector();
    });
    els.channelList.appendChild(btn);
  }
}

function renderInstrument() {
  const inst = song.instruments[selectedChannel];
  const presets = presetsForChannel(selectedChannel);
  els.instPreset.innerHTML =
    `<option value="">Custom…</option>` +
    presets
      .map(
        (p) =>
          `<option value="${p.id}" ${p.id === inst.id ? "selected" : ""}>${p.name}</option>`,
      )
      .join("");
  els.instName.value = inst.name;
  els.instDuty.value = String(inst.duty);
  els.instVolume.value = String(inst.volume);
  els.instVolumeOut.textContent = String(inst.volume);
  els.instArp.value = inst.arpMacro.join(" ");
  els.instPitch.value = (inst.pitchMacro || []).join(" ");
  els.instVibSpeed.value = String(inst.vibratoSpeed || 0);
  els.instVibDepth.value = String(inst.vibratoDepth || 0);
  els.instDelay.value = String(inst.delay || 0);
  els.instSpeed.value = String(inst.macroSpeed);
  els.instShortNoise.checked = inst.shortNoise;
  const isPulse = selectedChannel === "pulse1" || selectedChannel === "pulse2";
  const isNoise = selectedChannel === "noise";
  els.instDuty.disabled = !isPulse;
  els.instNoiseWrap.hidden = !isNoise;
  els.instDuty.title = isPulse ? DUTY_LABELS[inst.duty] : "Pulse only";
}

function parseIntList(text, signed = false) {
  if (!text.trim()) return [];
  return text
    .trim()
    .split(/[\s,]+/)
    .map((n) => Number(n))
    .filter((n) => Number.isFinite(n))
    .map((n) => {
      const v = n | 0;
      return signed ? Math.max(-64, Math.min(64, v)) : Math.max(0, Math.min(15, v));
    })
    .slice(0, 32);
}

function applyInstrumentFromForm() {
  const inst = song.instruments[selectedChannel];
  inst.name = els.instName.value.trim() || inst.name;
  inst.duty = Number(els.instDuty.value) | 0;
  inst.volume = Number(els.instVolume.value) | 0;
  inst.arpMacro = parseIntList(els.instArp.value, true).map((n) =>
    Math.max(-24, Math.min(24, n)),
  );
  inst.pitchMacro = parseIntList(els.instPitch.value, true);
  inst.vibratoSpeed = Math.max(0, Number(els.instVibSpeed.value) | 0);
  inst.vibratoDepth = Math.max(0, Number(els.instVibDepth.value) | 0);
  inst.delay = Math.max(0, Number(els.instDelay.value) | 0);
  inst.macroSpeed = Math.max(1, Number(els.instSpeed.value) | 0);
  inst.shortNoise = els.instShortNoise.checked;
  els.instVolumeOut.textContent = String(inst.volume);
  persist();
  syncEngineSong();
  renderChannels();
}

function renderPatterns() {
  els.patternTabs.innerHTML = "";
  song.patterns.forEach((p, i) => {
    const btn = document.createElement("button");
    btn.type = "button";
    btn.className = "btn tiny";
    btn.textContent = p.name || String.fromCharCode(65 + i);
    btn.setAttribute(
      "aria-pressed",
      i === song.editPattern ? "true" : "false",
    );
    btn.addEventListener("click", () => {
      song = selectEditPattern(song, i);
      selectedStep = 0;
      persist();
      els.length.value = String(editPattern().length);
      renderAll();
    });
    els.patternTabs.appendChild(btn);
  });
}

function renderOrder() {
  els.orderList.innerHTML = "";
  song.order.forEach((patIdx, orderIdx) => {
    const chip = document.createElement("button");
    chip.type = "button";
    chip.className = "order-chip";
    if (playing && orderIdx === playheadOrder) chip.classList.add("is-playing");
    const name =
      song.patterns[patIdx]?.name || String.fromCharCode(65 + patIdx);
    chip.textContent = name;
    chip.title = "Click to remove from order";
    chip.addEventListener("click", () => {
      song = removeOrderEntry(song, orderIdx);
      persist();
      syncEngineSong();
      renderOrder();
    });
    els.orderList.appendChild(chip);
  });
}

function renderGrid() {
  const pattern = editPattern();
  const len = pattern.length;
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
      const note = pattern.tracks[ch][i];
      if (note?.cut) {
        cell.classList.add("has-note", "is-cut");
        cell.textContent = "✕";
        cell.title = "Cut";
      } else if (note) {
        cell.classList.add("has-note");
        cell.textContent = formatNoteName(note.midi);
        const bits = [formatNoteName(note.midi)];
        if (note.slideTo != null) bits.push(`→${formatNoteName(note.slideTo)}`);
        if (note.gate != null && note.gate !== TICKS_PER_STEP) {
          bits.push(`g${note.gate}`);
        }
        cell.title = bits.join(" ");
      }
      if (i === selectedStep && ch === selectedChannel) {
        cell.classList.add("is-selected");
      }
      if (
        playing &&
        i === playheadStep &&
        song.order[playheadOrder] === song.editPattern
      ) {
        cell.classList.add("is-playhead");
      }
      cell.addEventListener("click", () => onCellClick(ch, i));
      cell.addEventListener("contextmenu", (event) => {
        event.preventDefault();
        song = setEditPatternData(
          song,
          clearStep(editPattern(), ch, i),
        );
        persist();
        syncEngineSong();
        renderGrid();
        renderNoteInspector();
      });
      row.appendChild(cell);
    }
    els.stepGrid.appendChild(row);
  }
}

function highlightPlayhead() {
  for (const cell of els.stepGrid.querySelectorAll(".step-cell")) {
    const step = Number(cell.dataset.step);
    const onEdit =
      playing &&
      song.order[playheadOrder] === song.editPattern &&
      step === playheadStep;
    cell.classList.toggle("is-playhead", onEdit);
  }
  updateTransportUi();
}

function renderNoteInspector() {
  const note = getStep(editPattern(), selectedChannel, selectedStep);
  if (!note || note.cut) {
    els.noteInspector.hidden = !note?.cut;
    if (note?.cut) {
      els.noteLength.disabled = true;
      els.noteGate.disabled = true;
      els.noteSlide.disabled = true;
    }
    return;
  }
  els.noteInspector.hidden = false;
  els.noteLength.disabled = false;
  els.noteGate.disabled = false;
  els.noteSlide.disabled = false;
  els.noteLength.value = String(note.length ?? 1);
  els.noteGate.value = String(note.gate ?? TICKS_PER_STEP);
  els.noteSlide.value = String(note.slideTo ?? -1);
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
  renderNoteInspector();
}

function applyNoteInspector() {
  const note = getStep(editPattern(), selectedChannel, selectedStep);
  if (!note || note.cut) return;
  const length = Math.max(1, Number(els.noteLength.value) | 0);
  const gate = Math.max(1, Math.min(TICKS_PER_STEP, Number(els.noteGate.value) | 0));
  const slideRaw = Number(els.noteSlide.value);
  /** @type {import("./sequencer/pattern.js").StepNote} */
  const next = {
    midi: note.midi,
    length,
    gate,
  };
  if (note.velocity != null) next.velocity = note.velocity;
  if (Number.isFinite(slideRaw) && slideRaw >= 0) next.slideTo = slideRaw | 0;
  song = setEditPatternData(
    song,
    setStep(editPattern(), selectedChannel, selectedStep, next),
  );
  persist();
  syncEngineSong();
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
    // Record into the pattern currently playing in the order.
    const patIdx = song.order[playheadOrder] ?? song.editPattern;
    const pattern = song.patterns[patIdx];
    song.patterns[patIdx] = overdubNote(pattern, ch, step, midi, { velocity });
    song = { ...song, patterns: [...song.patterns] };
    persist();
    syncEngineSong();
    if (patIdx === song.editPattern) renderGrid();
  } else if (!playing) {
    song = setEditPatternData(
      song,
      overdubNote(editPattern(), ch, selectedStep, midi, { velocity }),
    );
    selectedStep = (selectedStep + 1) % editPattern().length;
    persist();
    syncEngineSong();
    renderGrid();
    renderNoteInspector();
  }
}

function handleNoteOff(_midi) {
  engine.noteOff(selectedChannel);
}

function updateOctaveLabel() {
  els.octaveLabel.textContent = formatNoteName(octaveBase);
}

function renderAll() {
  renderChannels();
  renderInstrument();
  renderPatterns();
  renderOrder();
  renderGrid();
  renderNoteInspector();
  updateTransportUi();
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

// Cut shortcut when a cell is selected and user presses Shift+X (avoid stealing piano X)
window.addEventListener("keydown", (event) => {
  if (event.key !== "X" || !event.shiftKey) return;
  const tag = document.activeElement?.tagName;
  if (tag === "INPUT" || tag === "SELECT" || tag === "TEXTAREA") return;
  event.preventDefault();
  song = setEditPatternData(
    song,
    setCut(editPattern(), selectedChannel, selectedStep),
  );
  persist();
  syncEngineSong();
  renderGrid();
  renderNoteInspector();
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
  playheadOrder = 0;
  updateTransportUi();
  highlightPlayhead();
  renderOrder();
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
  song = setEditPatternData(song, resizePattern(editPattern(), length));
  if (selectedStep >= editPattern().length) selectedStep = 0;
  persist();
  syncEngineSong();
  renderGrid();
});

els.demo.addEventListener("click", () => {
  song = createDemoSong();
  els.bpm.value = String(song.bpm);
  els.length.value = String(editPattern().length);
  persist();
  syncEngineSong();
  renderAll();
});

els.clear.addEventListener("click", () => {
  song = createSong({
    title: "Untitled",
    bpm: song.bpm,
    length: editPattern().length,
  });
  persist();
  syncEngineSong();
  renderAll();
});

els.exportBtn.addEventListener("click", async () => {
  els.exportBtn.disabled = true;
  els.exportBtn.textContent = "Rendering…";
  try {
    await new Promise((r) => setTimeout(r, 20));
    const blob = songToWavBlob(song, { loops: 1, sampleRate: 44100 });
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

els.exportNsfBtn.addEventListener("click", async () => {
  els.exportNsfBtn.disabled = true;
  els.exportNsfBtn.textContent = "Building…";
  try {
    await new Promise((r) => setTimeout(r, 20));
    const blob = songToNsfBlob(song, { loops: 1 });
    const url = URL.createObjectURL(blob);
    const a = document.createElement("a");
    a.href = url;
    a.download = `${slugify(song.title) || "nes-seq"}.nsf`;
    a.click();
    URL.revokeObjectURL(url);
  } finally {
    els.exportNsfBtn.disabled = false;
    els.exportNsfBtn.textContent = "Export NSF";
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

els.patAdd.addEventListener("click", () => {
  song = addPattern(song);
  persist();
  syncEngineSong();
  els.length.value = String(editPattern().length);
  renderAll();
});
els.patDup.addEventListener("click", () => {
  song = duplicateEditPattern(song);
  persist();
  syncEngineSong();
  renderAll();
});
els.patDel.addEventListener("click", () => {
  song = deletePattern(song, song.editPattern);
  persist();
  syncEngineSong();
  els.length.value = String(editPattern().length);
  renderAll();
});
els.orderAdd.addEventListener("click", () => {
  song = appendOrder(song, song.editPattern);
  persist();
  syncEngineSong();
  renderOrder();
});

els.instPreset.addEventListener("change", () => {
  const id = els.instPreset.value;
  if (!id) return;
  const preset = createDefaultInstruments().find((i) => i.id === id);
  if (!preset) return;
  song.instruments[selectedChannel] = {
    ...cloneInstrument(preset),
    channel: selectedChannel,
  };
  persist();
  syncEngineSong();
  renderInstrument();
  renderChannels();
});

for (const el of [
  els.instName,
  els.instDuty,
  els.instVolume,
  els.instArp,
  els.instPitch,
  els.instVibSpeed,
  els.instVibDepth,
  els.instDelay,
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

for (const el of [els.noteLength, els.noteGate, els.noteSlide]) {
  el.addEventListener("change", applyNoteInspector);
}

els.noteCut.addEventListener("click", () => {
  song = setEditPatternData(
    song,
    setCut(editPattern(), selectedChannel, selectedStep),
  );
  persist();
  syncEngineSong();
  renderGrid();
  renderNoteInspector();
});

function slugify(text) {
  return String(text)
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, "-")
    .replace(/(^-|-$)/g, "");
}

function boot() {
  els.bpm.value = String(song.bpm);
  els.length.value = String(editPattern().length);
  if (!isMidiSupported()) {
    els.statusMidi.textContent = "MIDI: unsupported (use Chrome/Firefox)";
    els.midiBtn.disabled = true;
  }
  renderAll();
  updateOctaveLabel();
  keyboard.attach();
  window.__nesSeq = {
    getSong: () => songToJSON(song),
    engine,
  };
}

boot();
