import { SectionPlayer, tickSeconds } from "./audio-engine.js";
import { opcodeRows, pitchToMidi, sections } from "./music-data.js";

const $ = (selector, root = document) => root.querySelector(selector);

const tabs = $(".section-tabs");
const sequencer = $(".sequencer");
const codeList = $(".code-list");
const channelMix = $(".channel-mix");
const playButton = $(".play-button");
const playLabel = $(".play-label");
const playIcon = $(".play-icon");
const currentTime = $(".current-time");
const totalTime = $(".total-time");
const progressFill = $(".progress-track i");
const liveIndicator = $(".live-indicator");

let currentSection = sections[0];
let mutedChannels = new Set();
let currentTick = 0;

const player = new SectionPlayer({
  onFrame: ({ elapsed, progress, tick }) => {
    currentTick = tick;
    currentTime.textContent = formatPlaybackTime(elapsed);
    progressFill.style.width = `${progress * 100}%`;
    updatePlayhead(progress);
    updateActiveNotes(tick);
    updateActiveCode(tick);
  },
  onStop: resetTransport,
});

function formatPlaybackTime(seconds) {
  const minutes = Math.floor(seconds / 60);
  return `${minutes}:${(seconds % 60).toFixed(1).padStart(4, "0")}`;
}

function addressNumber(address) {
  return Number.parseInt(address?.replace("$", ""), 16);
}

function renderTabs() {
  tabs.replaceChildren(
    ...sections.map((section, index) => {
      const button = document.createElement("button");
      button.className = "section-tab";
      button.type = "button";
      button.role = "tab";
      button.id = `tab-${section.id}`;
      button.setAttribute("aria-controls", "passage-player");
      button.setAttribute("aria-selected", String(section.id === currentSection.id));
      button.tabIndex = section.id === currentSection.id ? 0 : -1;
      button.innerHTML = `<span>0${index + 1}</span><strong>${section.id.toUpperCase()}</strong>`;
      button.addEventListener("click", () => selectSection(section));
      button.addEventListener("keydown", (event) => {
        if (!["ArrowLeft", "ArrowRight"].includes(event.key)) return;
        event.preventDefault();
        const direction = event.key === "ArrowRight" ? 1 : -1;
        const next = (index + direction + sections.length) % sections.length;
        selectSection(sections[next]);
        tabs.children[next].focus();
      });
      return button;
    }),
  );
}

function selectSection(section) {
  player.stop(false);
  currentSection = section;
  mutedChannels = new Set();
  currentTick = 0;
  renderTabs();
  renderPassage();
  resetTransport();
}

function renderPassage() {
  $(".player-shell").id = "passage-player";
  $(".player-shell").setAttribute("aria-labelledby", `tab-${currentSection.id}`);
  $(".passage-eyebrow").textContent = currentSection.eyebrow;
  $(".passage-title").textContent = currentSection.title;
  $(".passage-summary").textContent = currentSection.summary;
  $(".insight-copy").textContent = currentSection.insight;
  totalTime.textContent = formatPlaybackTime(currentSection.durationTicks * tickSeconds);
  renderSequencer();
  renderCode();
  renderMixer();
}

function renderSequencer() {
  const allMidi = currentSection.channels
    .flatMap((channel) => channel.events)
    .map((event) => pitchToMidi(event.pitch))
    .filter((value) => value !== null);
  const lowest = Math.min(...allMidi);
  const highest = Math.max(...allMidi);
  const range = Math.max(12, highest - lowest);

  const playhead = document.createElement("i");
  playhead.className = "playhead";

  const rows = currentSection.channels.map((channel) => {
    const row = document.createElement("div");
    row.className = "sequence-row";
    row.dataset.channel = channel.id;
    row.style.color = channel.color;
    row.innerHTML = `<span class="row-name">${channel.name.toUpperCase()}</span>`;

    channel.events.forEach((event) => {
      if (!event.pitch) return;
      const block = document.createElement("i");
      block.className = "note-block";
      block.dataset.start = event.start;
      block.dataset.end = event.start + event.duration;
      block.style.left = `${(event.start / currentSection.durationTicks) * 100}%`;
      block.style.width = `${Math.max(0.65, (event.duration / currentSection.durationTicks) * 100)}%`;
      if (channel.wave === "noise") {
        block.style.top = "58%";
      } else {
        const midi = pitchToMidi(event.pitch);
        block.style.top = `${80 - ((midi - lowest) / range) * 60}%`;
      }
      block.title = `${event.pitch} · ${event.byte} · ${event.address}`;
      row.append(block);
    });
    return row;
  });

  sequencer.replaceChildren(playhead, ...rows);
}

function renderCode() {
  codeList.replaceChildren(
    ...currentSection.code.map((instruction, index) => {
      const row = document.createElement("div");
      row.className = "code-row";
      row.role = "listitem";
      row.dataset.index = index;
      row.dataset.address = addressNumber(instruction.address);
      row.innerHTML = `
        <span class="code-address">${instruction.address}</span>
        <span class="code-bytes">${instruction.bytes}</span>
        <span class="code-comment">; ${instruction.comment}</span>
        <span class="code-asm">${instruction.asm}</span>
      `;
      return row;
    }),
  );
}

function renderMixer() {
  channelMix.replaceChildren(
    ...currentSection.channels.map((channel) => {
      const button = document.createElement("button");
      button.type = "button";
      button.className = "mix-button";
      button.style.setProperty("--channel-color", channel.color);
      button.dataset.channel = channel.id;
      button.setAttribute("aria-pressed", "false");
      button.textContent = `MUTE ${channel.name.toUpperCase()}`;
      button.addEventListener("click", () => toggleChannel(channel.id, button));
      return button;
    }),
  );
}

function toggleChannel(channelId, button) {
  if (mutedChannels.has(channelId)) {
    mutedChannels.delete(channelId);
  } else {
    mutedChannels.add(channelId);
  }
  const muted = mutedChannels.has(channelId);
  button.setAttribute("aria-pressed", String(muted));
  $(`.sequence-row[data-channel="${channelId}"]`)?.classList.toggle("is-muted", muted);
  player.setMuted?.(channelId, muted);
}

function updatePlayhead(progress) {
  const playhead = $(".playhead", sequencer);
  if (playhead) playhead.style.left = `${progress * 100}%`;
}

function updateActiveNotes(tick) {
  sequencer.querySelectorAll(".note-block").forEach((block) => {
    const active = tick >= Number(block.dataset.start) && tick < Number(block.dataset.end);
    block.classList.toggle("is-active", active);
  });
}

function updateActiveCode(tick) {
  const primary = currentSection.channels[0];
  const event = primary.events.find(
    (candidate) => tick >= candidate.start && tick < candidate.start + candidate.duration,
  );
  const eventAddress = addressNumber(event?.address);
  const rows = [...codeList.querySelectorAll(".code-row")];
  let active = rows[0];

  if (Number.isFinite(eventAddress)) {
    rows.forEach((row) => {
      if (Number(row.dataset.address) <= eventAddress) active = row;
    });
  } else {
    active = rows[Math.min(rows.length - 1, Math.floor((tick / currentSection.durationTicks) * rows.length))];
  }

  rows.forEach((row) => row.classList.toggle("is-active", row === active));
  active?.scrollIntoView({ block: "nearest", behavior: "smooth" });
}

function resetTransport() {
  playButton.classList.remove("is-playing");
  playLabel.textContent = "Play passage";
  playIcon.textContent = "▶";
  liveIndicator.classList.remove("is-live");
  currentTime.textContent = "0:00.0";
  progressFill.style.width = "0";
  updatePlayhead(0);
  updateActiveNotes(-1);
  codeList.querySelectorAll(".code-row").forEach((row) => row.classList.remove("is-active"));
}

playButton.addEventListener("click", async () => {
  if (player.playing) {
    player.stop();
    return;
  }
  playButton.classList.add("is-playing");
  playLabel.textContent = "Stop";
  playIcon.textContent = "■";
  liveIndicator.classList.add("is-live");
  try {
    await player.play(currentSection, mutedChannels);
  } catch (error) {
    resetTransport();
    console.error("Unable to start Web Audio playback", error);
  }
});

opcodeRows.forEach(([opcode, name, description]) => {
  const row = document.createElement("div");
  row.className = "opcode-row";
  row.role = "row";
  row.innerHTML = `
    <span class="opcode" role="cell">${opcode}</span>
    <span class="opcode-name" role="cell">${name}</span>
    <span class="opcode-description" role="cell">${description}</span>
  `;
  $(".opcode-table").append(row);
});

renderTabs();
renderPassage();
resetTransport();
