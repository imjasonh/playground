import {
  CELLS,
  SIZE,
  SYMBOLS,
  formatGrid,
  formatSeed,
  generatePuzzle,
  parseLevel,
  parseSeed,
} from "./sudoku.js";

const DEFAULT_LEVEL = "medium";
const LEVEL_NAMES = { easy: "Easy", medium: "Medium", hard: "Hard" };
const COPY_LABEL_MS = 1500;

const boardBody = document.querySelector("#board tbody");
const statusEl = document.querySelector("#status");
const linkEl = document.querySelector("#link");
const levelInputs = [...document.querySelectorAll("input[name='level']")];
const newButton = document.querySelector("#new");
const solutionButton = document.querySelector("#solution");
const copyButton = document.querySelector("#copy");
const printButton = document.querySelector("#print");
const copyLabel = copyButton.textContent;

const cells = [];
for (let row = 0; row < SIZE; row += 1) {
  const tr = document.createElement("tr");
  for (let col = 0; col < SIZE; col += 1) {
    const td = document.createElement("td");
    tr.append(td);
    cells.push(td);
  }
  boardBody.append(tr);
}

const state = { board: null, showSolution: false };
let copyTimer = 0;

function randomSeed() {
  return crypto.getRandomValues(new Uint32Array(1))[0];
}

function render() {
  const { board, showSolution } = state;
  for (let i = 0; i < CELLS; i += 1) {
    const clue = board.puzzle[i];
    const cell = cells[i];
    if (clue !== 0) {
      cell.textContent = SYMBOLS[clue - 1];
      cell.className = "clue";
    } else if (showSolution) {
      cell.textContent = SYMBOLS[board.solution[i] - 1];
      cell.className = "answer";
    } else {
      cell.textContent = "";
      cell.className = "";
    }
  }
  for (const input of levelInputs) {
    input.checked = input.value === board.level;
  }
  solutionButton.setAttribute("aria-pressed", String(showSolution));
  statusEl.textContent = `${LEVEL_NAMES[board.level]} · ${board.clues} clues · Seed ${formatSeed(board.seed)}`;
  linkEl.textContent = window.location.href;
}

// Shows the board for level and seed and records both in the URL, so a
// reload or a shared link builds the same board. A pushed entry lets Back
// return to the previous board.
function showBoard(level, seed, historyMode) {
  const url = new URL(window.location.href);
  url.searchParams.set("level", level);
  url.searchParams.set("seed", formatSeed(seed));
  if (historyMode === "push") {
    window.history.pushState(null, "", url);
  } else {
    window.history.replaceState(null, "", url);
  }
  state.board = generatePuzzle(seed, level);
  state.showSolution = false;
  render();
}

function showBoardFromUrl() {
  const params = new URLSearchParams(window.location.search);
  const level = parseLevel(params.get("level")) ?? DEFAULT_LEVEL;
  const seed = parseSeed(params.get("seed")) ?? randomSeed();
  showBoard(level, seed, "replace");
}

newButton.addEventListener("click", () => {
  showBoard(state.board.level, randomSeed(), "push");
});

for (const input of levelInputs) {
  input.addEventListener("change", () => {
    showBoard(input.value, state.board.seed, "push");
  });
}

solutionButton.addEventListener("click", () => {
  state.showSolution = !state.showSolution;
  render();
});

copyButton.addEventListener("click", async () => {
  const { board, showSolution } = state;
  const grid = showSolution ? board.solution : board.puzzle;
  let label = "Copied";
  try {
    await navigator.clipboard.writeText(formatGrid(grid));
  } catch {
    label = "Copy failed";
  }
  copyButton.textContent = label;
  clearTimeout(copyTimer);
  copyTimer = setTimeout(() => {
    copyButton.textContent = copyLabel;
  }, COPY_LABEL_MS);
});

printButton.addEventListener("click", () => {
  window.print();
});

window.addEventListener("popstate", showBoardFromUrl);
showBoardFromUrl();
