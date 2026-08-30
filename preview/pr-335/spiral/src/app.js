import { generatePuzzleWithRetry } from "./generate.js";
import { spiralLayout, cellFontScale, cellRadiusScale } from "./spiral.js";
import {
  createPlayState,
  setLetter,
  clearGuesses,
  revealAll,
  checkGuesses,
  cellStatus,
  spanIndices,
  selectClue,
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
};

function formatRange(span) {
  return `${span.start}-${span.end}`;
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
    btn.addEventListener("click", () => {
      state = selectClue(state, dir, index);
      render();
      focusSpiral();
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

function renderSpiral() {
  if (!state) return;
  const { size } = state.puzzle;
  const layout = spiralLayout(size);
  const font = cellFontScale(size);
  const radius = cellRadiusScale(size);
  const hot = highlightSet();
  const vb = 1000;
  const parts = [];

  parts.push(
    `<svg viewBox="0 0 ${vb} ${vb}" role="img" aria-label="Spiral puzzle grid with ${size} cells">`,
  );
  // Soft guide path through cell centers.
  const path = layout
    .map((p, i) => `${i === 0 ? "M" : "L"} ${(p.x * vb).toFixed(1)} ${(p.y * vb).toFixed(1)}`)
    .join(" ");
  parts.push(`<path class="spiral-guide" d="${path}" />`);

  layout.forEach((p, i) => {
    const cx = p.x * vb;
    const cy = p.y * vb;
    const r = radius * vb;
    const status = cellStatus(state, i);
    const selected = state.selected === i;
    const inClue = hot.has(i);
    const classes = ["cell", `is-${status}`];
    if (selected) classes.push("is-selected");
    if (inClue) classes.push("is-clue");

    parts.push(`<g class="${classes.join(" ")}" data-index="${i}">`);
    parts.push(
      `<circle cx="${cx.toFixed(1)}" cy="${cy.toFixed(1)}" r="${r.toFixed(1)}" />`,
    );
    parts.push(
      `<text class="cell-num" x="${(cx - r * 0.55).toFixed(1)}" y="${(cy - r * 0.35).toFixed(1)}" font-size="${(font * vb * 0.55).toFixed(1)}">${i + 1}</text>`,
    );
    const letter = letterAt(state, i);
    if (letter) {
      parts.push(
        `<text class="cell-letter" x="${cx.toFixed(1)}" y="${(cy + font * vb * 0.35).toFixed(1)}" font-size="${(font * vb).toFixed(1)}">${letter}</text>`,
      );
    }
    parts.push("</g>");
  });

  parts.push("</svg>");
  els.spiral.innerHTML = parts.join("");

  els.spiral.querySelectorAll(".cell").forEach((node) => {
    node.addEventListener("click", () => {
      const index = Number(node.getAttribute("data-index"));
      state = { ...state, selected: index };
      // Prefer the inward clue covering this cell; fall back to outward.
      const inwardIdx = state.puzzle.inward.findIndex(
        (span) => index + 1 >= Math.min(span.start, span.end) && index + 1 <= Math.max(span.start, span.end),
      );
      if (inwardIdx >= 0) state = selectClue(state, "inward", inwardIdx);
      else {
        const outwardIdx = state.puzzle.outward.findIndex(
          (span) => index + 1 >= Math.min(span.start, span.end) && index + 1 <= Math.max(span.start, span.end),
        );
        if (outwardIdx >= 0) state = selectClue(state, "outward", outwardIdx);
      }
      render();
      focusSpiral();
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
  renderStatus();
}

function focusSpiral() {
  els.spiral.focus({ preventScroll: true });
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

function onKeyDown(event) {
  if (!state) return;
  if (event.metaKey || event.ctrlKey || event.altKey) return;

  const key = event.key;
  if (key === "ArrowRight" || key === "ArrowDown") {
    event.preventDefault();
    advanceSelection(1);
    render();
    return;
  }
  if (key === "ArrowLeft" || key === "ArrowUp") {
    event.preventDefault();
    advanceSelection(-1);
    render();
    return;
  }
  if (key === "Backspace" || key === "Delete") {
    event.preventDefault();
    state = setLetter(state, state.selected, "");
    if (key === "Backspace") advanceSelection(-1);
    render();
    return;
  }
  if (/^[a-zA-Z]$/.test(key)) {
    event.preventDefault();
    state = setLetter(state, state.selected, key);
    advanceSelection(1);
    render();
  }
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

  // Yield so the status can paint before a longer search.
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
    focusSpiral();
  });
}

function init() {
  const query = readQuery();
  for (const size of SIZES) {
    const opt = document.createElement("option");
    opt.value = String(size);
    opt.textContent = `${size} cells`;
    if (size === (query.size ?? 48)) opt.selected = true;
    els.size.appendChild(opt);
  }

  els.generate.addEventListener("click", () => newPuzzle());
  els.check.addEventListener("click", () => {
    if (!state) return;
    state = checkGuesses(state);
    render();
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
  });

  els.spiral.tabIndex = 0;
  els.spiral.addEventListener("keydown", onKeyDown);
  document.addEventListener("keydown", (event) => {
    if (event.target !== document.body && event.target !== els.spiral) return;
    onKeyDown(event);
  });

  newPuzzle(query.seed);
}

init();
