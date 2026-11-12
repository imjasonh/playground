import {
  EMPTY,
  GAMES,
  STAR,
  UNKNOWN,
  formatSeed,
  parseGame,
  parseLevel,
  parseSeed,
} from './puzzle.js';
import {
  REGION_NAMES,
  conflicts,
  cycleMark,
  dots,
  findHint,
  isWon,
  shapeOf,
} from './game.js';

const DEFAULT_GAME = 'queens';
const DEFAULT_LEVEL = 'easy';
const STORAGE_KEY = 'queens:v1';
const LEVEL_NAMES = {
  easy: 'Easy',
  medium: 'Medium',
  hard: 'Hard',
  expert: 'Expert',
};
const RULES_TEXT = {
  queens: 'Place one queen in every row, every column, and every colored ' +
      "region. Queens can't touch, not even at a corner.",
  twonottouch: 'Place two stars in every row, every column, and every ' +
      "colored region. Stars can't touch, not even at a corner.",
};
// Leaves time for the stars to pop before the dialog covers them.
const WIN_DIALOG_DELAY_MS = 900;

const titleEl = document.querySelector('#title');
const boardEl = document.querySelector('#board');
const infoEl = document.querySelector('#info');
const timerEl = document.querySelector('#timer');
const messageEl = document.querySelector('#message');
const rulesEl = document.querySelector('#rules');
const controlsEl = document.querySelector('#controls');
const gameInputs = [...document.querySelectorAll('input[name="game"]')];
const levelInputs = [...document.querySelectorAll('input[name="level"]')];
const undoButton = document.querySelector('#undo');
const clearButton = document.querySelector('#clear');
const autoButton = document.querySelector('#auto');
const hintButton = document.querySelector('#hint');
const newButton = document.querySelector('#new');
const wonDialog = document.querySelector('#won');
const wonText = document.querySelector('#won-text');
const reducedMotion = window.matchMedia('(prefers-reduced-motion: reduce)');

const state = {
  game: DEFAULT_GAME,
  level: DEFAULT_LEVEL,
  puzzle: null,
  shape: null,
  marks: null,
  history: [],
  hint: null,
  hints: 0,
  elapsed: 0,
  startedAt: null,
  solved: false,
  autoX: true,
};
let cells = [];
let loadToken = 0;
let drag = null;
let prefetched = null;

// Puzzles by key, as promises. The foreground worker builds the puzzle on
// screen and the background worker builds the next one, so a slow
// background build never holds up the board.
const puzzles = new Map();
const resolvers = new Map();
const workers = {foreground: null, background: null};
const busy = {foreground: new Set(), background: new Set()};

function startWorker(lane) {
  const worker = new Worker(new URL('./worker.js', import.meta.url),
      {type: 'module'});
  worker.addEventListener('message', (event) => {
    const {key, puzzle} = event.data;
    busy[lane].delete(key);
    resolvers.get(key)?.(puzzle);
    resolvers.delete(key);
  });
  workers[lane] = worker;
}

function puzzleKey(game, level, seed) {
  return `${game}:${level}:${formatSeed(seed)}`;
}

function requestPuzzle(game, level, seed, lane) {
  const key = puzzleKey(game, level, seed);
  if (puzzles.has(key)) {
    return puzzles.get(key);
  }
  // A new board on screen replaces any the foreground worker is still
  // building.
  if (lane === 'foreground' && busy.foreground.size > 0) {
    workers.foreground.terminate();
    for (const stale of busy.foreground) {
      puzzles.delete(stale);
      resolvers.delete(stale);
    }
    busy.foreground.clear();
    startWorker(lane);
  }
  if (!workers[lane]) {
    startWorker(lane);
  }
  const promise = new Promise((resolve) => {
    resolvers.set(key, resolve);
  });
  puzzles.set(key, promise);
  busy[lane].add(key);
  workers[lane].postMessage({key, game, level, seed});
  return promise;
}

function randomSeed() {
  return crypto.getRandomValues(new Uint32Array(1))[0];
}

// Builds the next puzzle at the current game and level in the background,
// so New shows it at once.
function prefetch() {
  prefetched = {game: state.game, level: state.level, seed: randomSeed()};
  requestPuzzle(prefetched.game, prefetched.level, prefetched.seed,
      'background');
  const keep = new Set([
    puzzleKey(state.game, state.level, state.puzzle.seed),
    puzzleKey(prefetched.game, prefetched.level, prefetched.seed),
  ]);
  for (const key of puzzles.keys()) {
    if (!keep.has(key)) {
      puzzles.delete(key);
    }
  }
}

function loadSaved() {
  try {
    return JSON.parse(localStorage.getItem(STORAGE_KEY)) ?? {};
  } catch {
    return {};
  }
}

function save() {
  const saved = {autoX: state.autoX};
  if (state.puzzle) {
    Object.assign(saved, {
      game: state.game,
      level: state.level,
      seed: formatSeed(state.puzzle.seed),
      marks: state.marks.join(''),
      elapsed: Math.round(elapsedMs()),
      hints: state.hints,
      solved: state.solved,
    });
  }
  try {
    localStorage.setItem(STORAGE_KEY, JSON.stringify(saved));
  } catch {
    // Storage can be full or turned off; the puzzle still plays.
  }
}

function elapsedMs() {
  const running = state.startedAt === null ?
      0 : performance.now() - state.startedAt;
  return state.elapsed + running;
}

function startTimer() {
  if (state.puzzle && state.startedAt === null && !state.solved &&
      !document.hidden) {
    state.startedAt = performance.now();
  }
}

function stopTimer() {
  state.elapsed = elapsedMs();
  state.startedAt = null;
}

function formatTime(ms) {
  const seconds = Math.floor(ms / 1000);
  const minutes = Math.floor(seconds / 60);
  const rest = String(seconds % 60).padStart(2, '0');
  if (minutes < 60) {
    return `${minutes}:${rest}`;
  }
  const hours = Math.floor(minutes / 60);
  return `${hours}:${String(minutes % 60).padStart(2, '0')}:${rest}`;
}

function renderTimer() {
  timerEl.textContent = formatTime(elapsedMs());
}

function pieceNames() {
  return GAMES[state.game].stars === 1 ?
      {one: 'queen', many: 'queens', symbol: '#queen'} :
      {one: 'star', many: 'stars', symbol: '#star'};
}

function buildBoard() {
  const {size, regions} = state.puzzle;
  boardEl.style.setProperty('--n', String(size));
  boardEl.classList.remove('won');
  cells = [];
  const rows = [];
  for (let r = 0; r < size; r += 1) {
    const row = document.createElement('div');
    row.className = 'row';
    row.setAttribute('role', 'row');
    for (let c = 0; c < size; c += 1) {
      const i = r * size + c;
      const cell = document.createElement('div');
      cell.className = 'cell';
      cell.setAttribute('role', 'gridcell');
      cell.tabIndex = -1;
      cell.dataset.index = String(i);
      cell.style.setProperty('--region', `var(--r${regions[i]})`);
      const differs = (rr, cc) => rr >= 0 && rr < size && cc >= 0 &&
          cc < size && regions[rr * size + cc] !== regions[i];
      cell.classList.toggle('edge-top', differs(r - 1, c));
      cell.classList.toggle('edge-left', differs(r, c - 1));
      cell.classList.toggle('edge-right', differs(r, c + 1));
      cell.classList.toggle('edge-bottom', differs(r + 1, c));
      cell.classList.toggle('last-col', c === size - 1);
      cell.classList.toggle('last-row', r === size - 1);
      row.append(cell);
      cells.push(cell);
    }
    rows.push(row);
  }
  cells[0].tabIndex = 0;
  boardEl.replaceChildren(...rows);
}

function statusText() {
  const {many} = pieceNames();
  if (state.solved) {
    return `Solved in ${formatTime(elapsedMs())}.`;
  }
  const {size, stars} = state.puzzle;
  const placed = state.marks.filter((mark) => mark === STAR).length;
  const total = size * stars;
  if (placed === 0) {
    return `Place ${total} ${many}.`;
  }
  return `${placed} of ${total} ${many} placed.`;
}

function render() {
  const {puzzle, shape, marks} = state;
  const {one, symbol} = pieceNames();
  const bad = conflicts(shape, marks);
  const dotted = state.autoX ? dots(shape, marks) : new Set();
  const targets = new Set(state.hint?.cells);
  const reasons = new Set(state.hint?.reason);
  let order = 0;
  for (let i = 0; i < cells.length; i += 1) {
    const cell = cells[i];
    const mark = marks[i];
    const name = mark === STAR ? 'star' : mark === EMPTY ? 'x' : '';
    if ((cell.dataset.mark ?? '') !== name) {
      if (name) {
        cell.dataset.mark = name;
      } else {
        delete cell.dataset.mark;
      }
      cell.replaceChildren();
      if (mark === STAR) {
        const svg = document.createElementNS('http://www.w3.org/2000/svg',
            'svg');
        svg.setAttribute('aria-hidden', 'true');
        const use = document.createElementNS('http://www.w3.org/2000/svg',
            'use');
        use.setAttribute('href', symbol);
        svg.append(use);
        cell.append(svg);
      }
    }
    if (mark === STAR) {
      cell.style.setProperty('--order', String(order));
      order += 1;
    }
    cell.classList.toggle('conflict', bad.has(i));
    cell.classList.toggle('dot', dotted.has(i));
    cell.classList.toggle('hint-target', targets.has(i));
    cell.classList.toggle('hint-reason', reasons.has(i) && !targets.has(i));
    const parts = [
      `Row ${Math.floor(i / puzzle.size) + 1}`,
      `column ${(i % puzzle.size) + 1}`,
      `${REGION_NAMES[puzzle.regions[i]]} region`,
    ];
    if (mark === STAR) {
      parts.push(bad.has(i) ? `${one}, conflict` : one);
    } else if (mark === EMPTY) {
      parts.push('marked ×');
    } else if (dotted.has(i)) {
      parts.push('ruled out');
    }
    cell.setAttribute('aria-label', parts.join(', '));
  }
  boardEl.classList.toggle('hinting', reasons.size > 0);
  messageEl.textContent = state.hint?.text ?? statusText();
  messageEl.classList.toggle('hint', Boolean(state.hint));
  undoButton.disabled = state.solved || state.history.length === 0;
  clearButton.disabled = state.solved ||
      marks.every((mark) => mark === UNKNOWN);
  hintButton.disabled = state.solved;
  autoButton.setAttribute('aria-pressed', String(state.autoX));
  renderTimer();
}

function renderChrome() {
  const {name} = GAMES[state.game];
  const {one, many} = pieceNames();
  titleEl.textContent = name;
  document.title = name;
  for (const input of gameInputs) {
    input.checked = input.value === state.game;
  }
  for (const input of levelInputs) {
    input.checked = input.value === state.level;
  }
  const {size} = GAMES[state.game].levels[state.level];
  infoEl.textContent = `${LEVEL_NAMES[state.level]} · ${size}×${size}`;
  rulesEl.textContent = RULES_TEXT[state.game];
  controlsEl.textContent = 'Tap a cell once to mark it ×, again for a ' +
      `${one}, and again to clear it. Drag across cells to mark them all ` +
      `×. With Auto × on, dots fill the cells your ${many} rule out.`;
}

// Shows the puzzle for game, level, and seed and records them in the URL,
// so a reload or a shared link shows the same puzzle. A pushed entry lets
// Back return to the previous puzzle.
async function showPuzzle(game, level, seed, historyMode) {
  const url = new URL(window.location.href);
  url.searchParams.set('game', game);
  url.searchParams.set('level', level);
  url.searchParams.set('seed', formatSeed(seed));
  if (historyMode === 'push') {
    window.history.pushState(null, '', url);
  } else {
    window.history.replaceState(null, '', url);
  }
  if (state.puzzle) {
    stopTimer();
    save();
  }
  state.game = game;
  state.level = level;
  renderChrome();
  wonDialog.close();
  loadToken += 1;
  const token = loadToken;
  boardEl.setAttribute('aria-busy', 'true');
  const puzzle = await requestPuzzle(game, level, seed, 'foreground');
  if (token !== loadToken) {
    return;
  }
  const saved = loadSaved();
  const resume = saved.game === game && saved.level === level &&
      saved.seed === formatSeed(seed) &&
      saved.marks?.length === puzzle.size * puzzle.size;
  Object.assign(state, {
    puzzle,
    shape: shapeOf(puzzle),
    marks: resume ?
        Uint8Array.from(saved.marks, Number) :
        new Uint8Array(puzzle.size * puzzle.size),
    history: [],
    hint: null,
    hints: resume ? saved.hints ?? 0 : 0,
    elapsed: resume ? saved.elapsed ?? 0 : 0,
    startedAt: null,
    solved: resume && Boolean(saved.solved),
  });
  buildBoard();
  boardEl.classList.toggle('won', state.solved);
  boardEl.setAttribute('aria-busy', 'false');
  startTimer();
  render();
  save();
  prefetch();
}

function showPuzzleFromUrl() {
  const params = new URLSearchParams(window.location.search);
  const saved = loadSaved();
  state.autoX = saved.autoX ?? true;
  let game = parseGame(params.get('game'));
  let level = parseLevel(params.get('level'));
  let seed = parseSeed(params.get('seed'));
  if (!game && !level && seed === null && parseGame(saved.game) &&
      parseLevel(saved.level) && parseSeed(saved.seed) !== null) {
    game = saved.game;
    level = saved.level;
    seed = parseSeed(saved.seed);
  }
  showPuzzle(game ?? DEFAULT_GAME, level ?? DEFAULT_LEVEL,
      seed ?? randomSeed(), 'replace');
}

function newPuzzle(game, level) {
  const ready = prefetched?.game === game && prefetched?.level === level;
  showPuzzle(game, level, ready ? prefetched.seed : randomSeed(), 'push');
}

function celebrate() {
  stopTimer();
  boardEl.classList.add('won');
  const {hints} = state;
  const used = hints === 0 ? 'no hints' :
      `${hints} ${hints === 1 ? 'hint' : 'hints'}`;
  wonText.textContent = `${GAMES[state.game].name}, ` +
      `${LEVEL_NAMES[state.level]}. Solved in ${formatTime(elapsedMs())} ` +
      `with ${used}.`;
  const token = loadToken;
  setTimeout(() => {
    if (token === loadToken && state.solved) {
      wonDialog.showModal();
    }
  }, reducedMotion.matches ? 0 : WIN_DIALOG_DELAY_MS);
}

// Records a move: a list of {index, before, after}. The marks may already
// show the move, as they do during a drag.
function commit(changes) {
  const real = changes.filter((change) => change.before !== change.after);
  if (real.length === 0) {
    return;
  }
  for (const {index, after} of real) {
    state.marks[index] = after;
  }
  state.history.push(real);
  state.hint = null;
  if (isWon(state.shape, state.marks)) {
    state.solved = true;
    celebrate();
  }
  render();
  save();
}

// Reports whether the board takes moves: a puzzle is showing, it isn't
// solved, and no other puzzle is loading.
function playable() {
  return state.puzzle !== null && !state.solved &&
      boardEl.getAttribute('aria-busy') !== 'true';
}

function cycleCell(index) {
  const before = state.marks[index];
  commit([{index, before, after: cycleMark(before)}]);
}

// Looks through every element at the point, not just the top one, so an
// overlay that a browser extension draws over the page doesn't hide the
// cell.
function cellAt(x, y) {
  const cell = document.elementsFromPoint(x, y)
      .find((el) => el.classList.contains('cell') && boardEl.contains(el));
  return cell ? Number(cell.dataset.index) : -1;
}

// Marks a cell during a drag: blanks become × when the drag started on a
// blank or a star, and × marks become blank when it started on a ×.
function paint(index) {
  const before = state.marks[index];
  const from = drag.paint === EMPTY ? UNKNOWN : EMPTY;
  if (before !== from || drag.changes.has(index)) {
    return;
  }
  drag.changes.set(index, {index, before, after: drag.paint});
  state.marks[index] = drag.paint;
}

function endDrag(event) {
  if (!drag || event.pointerId !== drag.pointerId) {
    return;
  }
  const {start, moved, changes} = drag;
  drag = null;
  if (moved) {
    commit([...changes.values()]);
  } else if (event.type === 'pointerup') {
    cycleCell(start);
  }
}

boardEl.addEventListener('pointerdown', (event) => {
  if (!event.isPrimary || event.button !== 0 || !playable()) {
    return;
  }
  const index = cellAt(event.clientX, event.clientY);
  if (index < 0) {
    return;
  }
  boardEl.setPointerCapture(event.pointerId);
  setActive(index);
  drag = {
    pointerId: event.pointerId,
    start: index,
    last: index,
    moved: false,
    paint: state.marks[index] === EMPTY ? UNKNOWN : EMPTY,
    changes: new Map(),
  };
});

boardEl.addEventListener('pointermove', (event) => {
  if (!drag || event.pointerId !== drag.pointerId) {
    return;
  }
  const index = cellAt(event.clientX, event.clientY);
  if (index < 0 || index === drag.last) {
    return;
  }
  if (!drag.moved) {
    drag.moved = true;
    paint(drag.start);
  }
  drag.last = index;
  paint(index);
  render();
});

boardEl.addEventListener('pointerup', endDrag);
boardEl.addEventListener('pointercancel', endDrag);

function setActive(index) {
  for (const cell of cells) {
    cell.tabIndex = -1;
  }
  cells[index].tabIndex = 0;
}

// Finds the cell next to current in the direction of an arrow key from the
// cells' positions on screen. Prefers cells in the same row or column.
function cellInDirection(current, key) {
  const from = current.getBoundingClientRect();
  const tolerance = 1;
  let best = null;
  let bestScore = Infinity;
  for (const cell of cells) {
    if (cell === current || !cell.checkVisibility()) {
      continue;
    }
    const to = cell.getBoundingClientRect();
    let gap;
    let overlaps;
    let offset;
    if (key === 'ArrowLeft' || key === 'ArrowRight') {
      gap = key === 'ArrowRight' ? to.left - from.right : from.left - to.right;
      overlaps = to.top < from.bottom && to.bottom > from.top;
      offset = Math.abs(to.top + to.height / 2 - from.top - from.height / 2);
    } else {
      gap = key === 'ArrowDown' ? to.top - from.bottom : from.top - to.bottom;
      overlaps = to.left < from.right && to.right > from.left;
      offset = Math.abs(to.left + to.width / 2 - from.left - from.width / 2);
    }
    if (gap < -tolerance) {
      continue;
    }
    // Aligned cells always beat the rest; among them the nearest wins.
    const score = overlaps ? gap + offset / 1000 : 1e6 + gap + 2 * offset;
    if (score < bestScore) {
      best = cell;
      bestScore = score;
    }
  }
  return best;
}

boardEl.addEventListener('keydown', (event) => {
  const [target] = event.composedPath();
  if (event.defaultPrevented || event.altKey || event.ctrlKey ||
      event.metaKey || !target.classList?.contains('cell')) {
    return;
  }
  if (event.key === ' ' || event.key === 'Enter') {
    event.preventDefault();
    if (playable()) {
      cycleCell(Number(target.dataset.index));
    }
    return;
  }
  if (!event.key.startsWith('Arrow')) {
    return;
  }
  const next = cellInDirection(target, event.key);
  if (!next) {
    return;
  }
  event.preventDefault();
  setActive(Number(next.dataset.index));
  next.focus();
  next.scrollIntoView({block: 'nearest', inline: 'nearest'});
});

undoButton.addEventListener('click', () => {
  if (!playable() || state.history.length === 0) {
    return;
  }
  const last = state.history.pop();
  for (const {index, before} of last) {
    state.marks[index] = before;
  }
  state.hint = null;
  render();
  save();
});

clearButton.addEventListener('click', () => {
  if (!playable()) {
    return;
  }
  const changes = [];
  state.marks.forEach((mark, index) => {
    if (mark !== UNKNOWN) {
      changes.push({index, before: mark, after: UNKNOWN});
    }
  });
  commit(changes);
});

autoButton.addEventListener('click', () => {
  state.autoX = !state.autoX;
  if (state.puzzle) {
    render();
  }
  save();
});

hintButton.addEventListener('click', () => {
  if (!playable() || state.hint) {
    return;
  }
  state.hint = findHint(state.puzzle, state.marks);
  if (state.hint) {
    state.hints += 1;
  }
  render();
  save();
});

newButton.addEventListener('click', () => {
  newPuzzle(state.game, state.level);
});

for (const input of gameInputs) {
  input.addEventListener('change', () => newPuzzle(input.value, state.level));
}

for (const input of levelInputs) {
  input.addEventListener('change', () => newPuzzle(state.game, input.value));
}

wonDialog.addEventListener('close', () => {
  if (wonDialog.returnValue === 'new') {
    newPuzzle(state.game, state.level);
  }
  wonDialog.returnValue = '';
});

document.addEventListener('visibilitychange', () => {
  if (document.hidden) {
    stopTimer();
    save();
  } else {
    startTimer();
  }
});

window.addEventListener('pagehide', save);
window.addEventListener('popstate', showPuzzleFromUrl);
setInterval(renderTimer, 500);
showPuzzleFromUrl();
