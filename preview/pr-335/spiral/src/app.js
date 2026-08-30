import { generatePuzzleWithRetry } from "./generate.js";
import { spiralLayout, cellFontScale, cellNumberScale } from "./spiral.js";
import {
  createPlayState,
  setLetter,
  clearGuesses,
  revealAll,
  checkGuesses,
  cellStatus,
  spanIndices,
  selectClue,
  cluesCovering,
  activeSpan,
  isSolved,
  filledCount,
  letterAt,
} from "./puzzle.js";

const SIZES = [36, 48, 64, 100];

/** @type {ReturnType<typeof createPlayState> | null} */
let state = null;

const els = {
  spiral: document.getElementById("spiral"),
  inward: document.getElementById("inward-clues"),
  outward: document.getElementById("outward-clues"),
  status: document.getElementById("status"),
  size: document.getElementById("size"),
  generate: document.getElementById("generate"),
  check: document.getElementById("check"),
  reveal: document.getElementById("reveal"),
  clear: document.getElementById("clear"),
  seed: document.getElementById("seed"),
  entry: document.getElementById("entry"),
  activeClue: document.getElementById("active-clue"),
  flipDir: document.getElementById("flip-dir"),
  activeRange: document.getElementById("active-clue-range"),
  activeText: document.getElementById("active-clue-text"),
};

function formatRange(span) {
  return `${span.start}-${span.end}`;
}

function focusEntry() {
  // Keep the caret ready so phone keyboards stay open after each letter.
  els.entry.focus({ preventScroll: true });
  try {
    const len = els.entry.value.length;
    els.entry.setSelectionRange(len, len);
  } catch {
    // Some browsers reject setSelectionRange on certain input types.
  }
}

function renderClues(container, dir) {
  if (!state) return;
  const list = state.puzzle[dir];
  container.replaceChildren();
  list.forEach((span, index) => {
    const btn = document.createElement("button");
    btn.type = "button";
    btn.className = "clue";
    if (state.activeDir === dir && state.activeClueIndex === index) {
      btn.classList.add("is-active");
    }
    const indices = spanIndices(span);
    const filled = indices.every((i) => state.guesses[i]);
    if (filled) btn.classList.add("is-filled");

    btn.innerHTML =
      `<span class="clue-range">${formatRange(span)}</span>` +
      `<span class="clue-text">${escapeHtml(span.clue)}</span>`;
    btn.addEventListener("pointerdown", (event) => {
      // Keep / open the soft keyboard; don't let the button steal focus.
      event.preventDefault();
      focusEntry();
    });
    btn.addEventListener("click", () => {
      state = selectClue(state, dir, index);
      render();
      focusEntry();
    });
    container.appendChild(btn);
  });
}

function escapeHtml(text) {
  return text
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;");
}

function highlightSet() {
  const span = activeSpan(state);
  return new Set(span ? spanIndices(span) : []);
}

function scalePath(path, vb) {
  return path.replace(
    /([ML])\s*([0-9.]+)\s+([0-9.]+)/g,
    (_, cmd, x, y) => `${cmd}${(Number(x) * vb).toFixed(1)} ${(Number(y) * vb).toFixed(1)}`,
  );
}

function selectCell(index, { toggleDir = false } = {}) {
  if (!state) return;
  const prefer = toggleDir
    ? state.activeDir === "inward"
      ? "outward"
      : "inward"
    : state.activeDir;
  const order = prefer === "outward" ? ["outward", "inward"] : ["inward", "outward"];

  let chosen = null;
  for (const dir of order) {
    const matches = cluesCovering(state.puzzle, dir, index);
    if (matches.length) {
      chosen = { dir, index: matches[0] };
      break;
    }
  }

  state = { ...state, selected: index };
  if (chosen) state = selectClue(state, chosen.dir, chosen.index);
  // Keep the tapped cell selected even if selectClue jumped to an empty one.
  state = { ...state, selected: index };
}

function renderActiveClue() {
  if (!state) {
    els.activeClue.hidden = true;
    return;
  }
  const span = activeSpan(state);
  if (!span) {
    els.activeClue.hidden = true;
    return;
  }
  els.activeClue.hidden = false;
  els.flipDir.textContent = state.activeDir === "inward" ? "Inward" : "Outward";
  els.activeRange.textContent = formatRange(span);
  els.activeText.textContent = span.clue;
}

function renderSpiral() {
  if (!state) return;
  const { size } = state.puzzle;
  const layout = spiralLayout(size);
  const font = cellFontScale(size, layout.trackWidth);
  const numFont = cellNumberScale(size, layout.trackWidth);
  const hot = highlightSet();
  const vb = 1000;
  const parts = [];

  parts.push(
    `<svg viewBox="0 0 ${vb} ${vb}" role="img" aria-label="Spiral puzzle grid with ${size} cells">`,
  );
  parts.push(
    `<circle class="spiral-rim" cx="${vb / 2}" cy="${vb / 2}" r="${0.48 * vb}" />`,
  );

  layout.cells.forEach((cell, i) => {
    const status = cellStatus(state, i);
    const selected = state.selected === i;
    const inClue = hot.has(i);
    const classes = ["cell", `is-${status}`];
    if (selected) classes.push("is-selected");
    if (inClue) classes.push("is-clue");

    parts.push(`<g class="${classes.join(" ")}" data-index="${i}">`);
    parts.push(`<path d="${scalePath(cell.path, vb)}" />`);
    parts.push(
      `<text class="cell-num" x="${(cell.numX * vb).toFixed(1)}" y="${(cell.numY * vb).toFixed(1)}" font-size="${(numFont * vb).toFixed(1)}">${i + 1}</text>`,
    );
    const letter = letterAt(state, i);
    if (letter) {
      parts.push(
        `<text class="cell-letter" x="${(cell.cx * vb).toFixed(1)}" y="${(cell.cy * vb).toFixed(1)}" font-size="${(font * vb).toFixed(1)}">${letter}</text>`,
      );
    }
    parts.push("</g>");
  });

  parts.push("</svg>");
  els.spiral.innerHTML = parts.join("");

  els.spiral.querySelectorAll(".cell").forEach((node) => {
    node.addEventListener("pointerdown", (event) => {
      event.preventDefault();
      focusEntry();
    });
    node.addEventListener("click", () => {
      const index = Number(node.getAttribute("data-index"));
      const sameCell = state && state.selected === index;
      selectCell(index, { toggleDir: sameCell });
      render();
      focusEntry();
    });
  });
}

function renderStatus() {
  if (!state) {
    els.status.textContent = "Generating…";
    return;
  }
  const filled = filledCount(state);
  const { size, seed } = state.puzzle;
  let message = `${filled}/${size} filled · seed ${seed}`;
  if (state.revealed) message = `Answer shown · seed ${seed}`;
  else if (isSolved(state)) message = `Solved · seed ${seed}`;
  else if (state.checked) message = `Checked · ${message}`;
  els.status.textContent = message;
  els.seed.textContent = String(seed);
}

function render() {
  renderSpiral();
  renderClues(els.inward, "inward");
  renderClues(els.outward, "outward");
  renderActiveClue();
  renderStatus();
}

function advanceSelection(delta) {
  if (!state) return;
  const span = activeSpan(state);
  if (!span) {
    state = {
      ...state,
      selected: (state.selected + delta + state.puzzle.size) % state.puzzle.size,
    };
    return;
  }
  const indices = spanIndices(span);
  const at = indices.indexOf(state.selected);
  if (at < 0) {
    state = { ...state, selected: indices[0] };
    return;
  }
  const next = at + delta;
  if (next >= 0 && next < indices.length) {
    state = { ...state, selected: indices[next] };
  }
}

function typeLetter(ch) {
  if (!state || state.revealed) return;
  state = setLetter(state, state.selected, ch);
  advanceSelection(1);
  render();
  focusEntry();
}

function deleteLetter({ goBack }) {
  if (!state || state.revealed) return;
  if (goBack && state.guesses[state.selected]) {
    state = setLetter(state, state.selected, "");
  } else if (goBack) {
    advanceSelection(-1);
    state = setLetter(state, state.selected, "");
  } else {
    state = setLetter(state, state.selected, "");
  }
  render();
  focusEntry();
}

function onKeyDown(event) {
  if (!state) return;
  if (event.metaKey || event.ctrlKey || event.altKey) return;

  // Ignore keydown letter repeats when the entry input will also fire input —
  // except for navigation / edit keys that input events do not cover well.
  const key = event.key;
  if (key === "ArrowRight" || key === "ArrowDown" || key === "Tab") {
    event.preventDefault();
    advanceSelection(key === "Tab" && event.shiftKey ? -1 : 1);
    render();
    focusEntry();
    return;
  }
  if (key === "ArrowLeft" || key === "ArrowUp") {
    event.preventDefault();
    advanceSelection(-1);
    render();
    focusEntry();
    return;
  }
  if (key === "Backspace") {
    event.preventDefault();
    deleteLetter({ goBack: true });
    return;
  }
  if (key === "Delete") {
    event.preventDefault();
    deleteLetter({ goBack: false });
    return;
  }
  if (key === " " || key === "Enter") {
    event.preventDefault();
    // Flip inward/outward for the selected cell.
    selectCell(state.selected, { toggleDir: true });
    render();
    focusEntry();
    return;
  }
  if (/^[a-zA-Z]$/.test(key) && event.target !== els.entry) {
    event.preventDefault();
    typeLetter(key);
  }
}

function onEntryInput() {
  const raw = els.entry.value;
  els.entry.value = "";
  const letters = raw.replace(/[^a-zA-Z]/g, "");
  if (!letters) return;
  // Mobile keyboards sometimes dump a whole word; take the last letter typed.
  typeLetter(letters.slice(-1));
}

function flipDirection() {
  if (!state) return;
  selectCell(state.selected, { toggleDir: true });
  render();
  focusEntry();
}

function readQuery() {
  const params = new URLSearchParams(window.location.search);
  const sizeParam = Number(params.get("size"));
  const seedParam = Number(params.get("seed"));
  return {
    size: SIZES.includes(sizeParam) ? sizeParam : null,
    seed: Number.isFinite(seedParam) ? seedParam >>> 0 : null,
  };
}

function writeQuery(puzzle) {
  const url = new URL(window.location.href);
  url.searchParams.set("size", String(puzzle.size));
  url.searchParams.set("seed", String(puzzle.seed));
  window.history.replaceState({}, "", url);
}

function newPuzzle(explicitSeed = null) {
  const size = Number(els.size.value) || 48;
  els.status.textContent = "Generating…";
  els.generate.disabled = true;

  requestAnimationFrame(() => {
    const puzzle = generatePuzzleWithRetry({
      size,
      seed: explicitSeed ?? undefined,
      attempts: explicitSeed == null ? 32 : 12,
      maxNodes: size * 16000,
    });
    els.generate.disabled = false;
    if (!puzzle) {
      els.status.textContent = "Could not generate a puzzle. Try again.";
      return;
    }
    state = createPlayState(puzzle);
    writeQuery(puzzle);
    render();
    focusEntry();
  });
}

function init() {
  const query = readQuery();
  for (const size of SIZES) {
    const opt = document.createElement("option");
    opt.value = String(size);
    opt.textContent = `${size} cells`;
    if (size === (query.size ?? 100)) opt.selected = true;
    els.size.appendChild(opt);
  }

  els.generate.addEventListener("click", () => newPuzzle());
  els.check.addEventListener("click", () => {
    if (!state) return;
    state = checkGuesses(state);
    render();
    focusEntry();
  });
  els.reveal.addEventListener("click", () => {
    if (!state) return;
    state = revealAll(state);
    render();
  });
  els.clear.addEventListener("click", () => {
    if (!state) return;
    state = clearGuesses(state);
    render();
    focusEntry();
  });

  els.flipDir.addEventListener("click", flipDirection);
  els.activeClue.addEventListener("click", (event) => {
    if (event.target === els.flipDir) return;
    focusEntry();
  });

  els.entry.addEventListener("keydown", onKeyDown);
  els.entry.addEventListener("input", onEntryInput);
  // Desktop: typing while focus is elsewhere still works.
  document.addEventListener("keydown", (event) => {
    if (event.target === els.entry) return;
    if (
      event.target instanceof HTMLInputElement ||
      event.target instanceof HTMLTextAreaElement ||
      event.target instanceof HTMLSelectElement ||
      (event.target instanceof HTMLElement && event.target.isContentEditable)
    ) {
      return;
    }
    onKeyDown(event);
  });

  // Tap the board background to reopen the keyboard.
  els.spiral.addEventListener("pointerdown", (event) => {
    if (event.target.closest(".cell")) return;
    event.preventDefault();
    focusEntry();
  });

  newPuzzle(query.seed);
}

init();
