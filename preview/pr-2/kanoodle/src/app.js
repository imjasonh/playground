import { ROWS, COLS, DIFFICULTY_LABELS } from './constants.js';
import { PIECES, getOrientations, pieceById, absoluteCells } from './pieces.js';

const orientationCache = Object.fromEntries(
  PIECES.map((piece) => [piece.id, getOrientations(piece.dots)])
);

const boardEl = document.getElementById('board');
const trayEl = document.getElementById('tray');
const statusEl = document.getElementById('status');
const difficultyEl = document.getElementById('difficulty');
const puzzleSelectEl = document.getElementById('puzzle-select');
const newGameBtn = document.getElementById('new-game');
const rotateBtn = document.getElementById('rotate-btn');
const flipBtn = document.getElementById('flip-btn');
const selectedPreviewEl = document.getElementById('selected-preview');
const previewShapeEl = document.getElementById('preview-shape');
const ghostLayerEl = document.getElementById('ghost-layer');

let game = null;
let dragState = null;

function init() {
  populatePuzzleSelect();
  bindControls();
  startNewGame();
}

function populatePuzzleSelect() {
  for (const puzzle of listLibraryPuzzles()) {
    const option = document.createElement('option');
    option.value = String(puzzle.id);
    option.textContent = `${puzzle.label} (level ${puzzle.difficulty})`;
    puzzleSelectEl.appendChild(option);
  }
}

function bindControls() {
  newGameBtn.addEventListener('click', startNewGame);
  rotateBtn.addEventListener('click', () => game?.rotateSelected());
  flipBtn.addEventListener('click', () => game?.flipSelected());

  document.addEventListener('keydown', (event) => {
    if (!game?.selectedPieceId) {
      return;
    }
    if (event.key === 'r' || event.key === 'R') {
      game.rotateSelected();
    }
    if (event.key === 'f' || event.key === 'F') {
      game.flipSelected();
    }
  });
}

function startNewGame() {
  const puzzleValue = puzzleSelectEl.value;
  const difficulty = Number(difficultyEl.value);
  const seed = Date.now();

  const state = puzzleValue
    ? createGameState({ puzzleId: Number(puzzleValue) })
    : createGameState({ difficulty, seed });

  game = new KanoodleGame(state);
  game.setOrientationCache(orientationCache);
  game.subscribe(render);
  render(game.getSnapshot());
}

function render(snapshot) {
  renderBoard(snapshot);
  renderTray(snapshot);
  renderStatus(snapshot);
  renderSelectedPreview(snapshot);
}

function renderStatus(snapshot) {
  const difficultyLabel = DIFFICULTY_LABELS[snapshot.difficulty] || '';
  if (snapshot.solved) {
    statusEl.textContent = 'Puzzle solved! Every noodle is in place.';
    statusEl.classList.add('win');
    return;
  }

  statusEl.classList.remove('win');
  const remaining = snapshot.trayPieces.length;
  statusEl.textContent = `${difficultyLabel} — ${remaining} piece${remaining === 1 ? '' : 's'} left to place.`;
}

function renderBoard(snapshot) {
  boardEl.innerHTML = '';
  ghostLayerEl.innerHTML = '';

  for (let row = 0; row < ROWS; row += 1) {
    for (let col = 0; col < COLS; col += 1) {
      const cell = document.createElement('div');
      cell.className = 'cell';
      cell.dataset.row = String(row);
      cell.dataset.col = String(col);

      const pieceId = snapshot.board[row][col];
      if (pieceId) {
        cell.classList.add('filled');
        cell.style.backgroundColor = pieceById(pieceId).color;
        if (snapshot.fixedPieces.has(pieceId)) {
          cell.classList.add('fixed');
        }
        cell.title = `Piece ${pieceId}${snapshot.fixedPieces.has(pieceId) ? ' (fixed)' : ''}`;

        cell.addEventListener('dblclick', () => {
          if (!snapshot.fixedPieces.has(pieceId)) {
            game.pickUpBoardPiece(pieceId);
          }
        });
      } else {
        cell.classList.add('empty');
      }

      cell.addEventListener('pointerdown', (event) => onBoardPointerDown(event, row, col, pieceId, snapshot));
      cell.addEventListener('pointerenter', () => highlightDropTarget(row, col, snapshot));
      cell.addEventListener('pointerleave', clearDropTargets);

      boardEl.appendChild(cell);
    }
  }
}

function renderTray(snapshot) {
  trayEl.innerHTML = '';

  if (snapshot.trayPieces.length === 0) {
    const empty = document.createElement('p');
    empty.className = 'empty-tray';
    empty.textContent = 'All pieces are on the board.';
    trayEl.appendChild(empty);
    return;
  }

  for (const pieceId of snapshot.trayPieces) {
    const piece = pieceById(pieceId);
    const item = document.createElement('div');
    item.className = 'tray-piece';
    item.dataset.pieceId = pieceId;
    if (snapshot.selectedPieceId === pieceId) {
      item.classList.add('selected');
    }

    const label = document.createElement('span');
    label.className = 'piece-label';
    label.textContent = `${piece.id} — ${piece.name}`;

    const orientation =
      snapshot.selectedPieceId === pieceId
        ? snapshot.selectedOrientation
        : orientationCache[pieceId][0];

    item.appendChild(label);
    item.appendChild(buildShapeElement(orientation, piece.color, 14));

    item.addEventListener('click', () => game.selectPiece(pieceId));
    item.addEventListener('pointerdown', (event) => startDragFromTray(event, pieceId));

    trayEl.appendChild(item);
  }
}

function renderSelectedPreview(snapshot) {
  if (!snapshot.selectedPieceId || !snapshot.selectedOrientation) {
    selectedPreviewEl.hidden = true;
    return;
  }

  selectedPreviewEl.hidden = false;
  previewShapeEl.innerHTML = '';
  const piece = pieceById(snapshot.selectedPieceId);
  previewShapeEl.appendChild(buildShapeElement(snapshot.selectedOrientation, piece.color, 18));
}

function buildShapeElement(orientation, color, dotSize) {
  const maxRow = Math.max(...orientation.map(([r]) => r));
  const maxCol = Math.max(...orientation.map(([, c]) => c));
  const wrap = document.createElement('div');
  wrap.className = 'piece-shape';
  wrap.style.gridTemplateColumns = `repeat(${maxCol + 1}, ${dotSize}px)`;
  wrap.style.gridTemplateRows = `repeat(${maxRow + 1}, ${dotSize}px)`;

  for (const [r, c] of orientation) {
    const dot = document.createElement('span');
    dot.className = 'piece-dot';
    dot.style.backgroundColor = color;
    dot.style.gridRow = String(r + 1);
    dot.style.gridColumn = String(c + 1);
    wrap.appendChild(dot);
  }

  return wrap;
}

function onBoardPointerDown(event, row, col, pieceId, snapshot) {
  if (pieceId && !snapshot.fixedPieces.has(pieceId)) {
    event.preventDefault();
    game.pickUpBoardPiece(pieceId);
    startDrag(event, pieceId, row, col);
    return;
  }

  if (snapshot.selectedPieceId) {
    event.preventDefault();
    startDrag(event, snapshot.selectedPieceId, row, col);
  }
}

function startDragFromTray(event, pieceId) {
  event.preventDefault();
  game.selectPiece(pieceId);
  startDrag(event, pieceId, null, null);
}

function startDrag(event, pieceId, anchorRow, anchorCol) {
  if (event.button !== 0) {
    return;
  }

  dragState = {
    pieceId,
    pointerId: event.pointerId,
    anchorRow,
    anchorCol,
    offsetRow: 0,
    offsetCol: 0,
  };

  if (anchorRow !== null && anchorCol !== null) {
    dragState.offsetRow = 0;
    dragState.offsetCol = 0;
  }

  document.addEventListener('pointermove', onDragMove);
  document.addEventListener('pointerup', onDragEnd);
  document.addEventListener('pointercancel', onDragEnd);
  showGhost(pieceId, anchorRow ?? 0, anchorCol ?? 0);
}

function onDragMove(event) {
  if (!dragState || event.pointerId !== dragState.pointerId) {
    return;
  }

  const cell = document.elementFromPoint(event.clientX, event.clientY)?.closest('.cell');
  if (cell) {
    const row = Number(cell.dataset.row);
    const col = Number(cell.dataset.col);
    showGhost(dragState.pieceId, row, col);
    highlightDropTarget(row, col, game.getSnapshot());
  }
}

function onDragEnd(event) {
  if (!dragState || event.pointerId !== dragState.pointerId) {
    return;
  }

  const cell = document.elementFromPoint(event.clientX, event.clientY)?.closest('.cell');
  if (cell) {
    const row = Number(cell.dataset.row);
    const col = Number(cell.dataset.col);
    game.selectPiece(dragState.pieceId);
    game.tryPlaceAt(row, col);
  }

  dragState = null;
  ghostLayerEl.innerHTML = '';
  clearDropTargets();
  document.removeEventListener('pointermove', onDragMove);
  document.removeEventListener('pointerup', onDragEnd);
  document.removeEventListener('pointercancel', onDragEnd);
}

function showGhost(pieceId, row, col) {
  const snapshot = game.getSnapshot();
  const orientation = snapshot.selectedOrientation || orientationCache[pieceId][0];
  const piece = pieceById(pieceId);
  const cells = absoluteCells(orientation, row, col);

  ghostLayerEl.hidden = false;
  ghostLayerEl.innerHTML = '';

  const boardRect = boardEl.getBoundingClientRect();
  const wrapRect = boardEl.parentElement.getBoundingClientRect();

  for (const [r, c] of cells) {
    if (r < 0 || r >= ROWS || c < 0 || c >= COLS) {
      continue;
    }
    const cellEl = boardEl.querySelector(`.cell[data-row="${r}"][data-col="${c}"]`);
    if (!cellEl) {
      continue;
    }
    const rect = cellEl.getBoundingClientRect();
    const dot = document.createElement('div');
    dot.className = 'piece-dot';
    dot.style.backgroundColor = piece.color;
    dot.style.position = 'absolute';
    dot.style.width = `${rect.width}px`;
    dot.style.height = `${rect.height}px`;
    dot.style.left = `${rect.left - wrapRect.left}px`;
    dot.style.top = `${rect.top - wrapRect.top}px`;
    dot.style.opacity = '0.6';
    dot.style.borderRadius = '50%';
    ghostLayerEl.appendChild(dot);
  }
}

function highlightDropTarget(row, col, snapshot) {
  if (!snapshot.selectedPieceId) {
    return;
  }

  clearDropTargets();
  const orientation = snapshot.selectedOrientation;
  if (!orientation) {
    return;
  }

  for (const [r, c] of absoluteCells(orientation, row, col)) {
    const cellEl = boardEl.querySelector(`.cell[data-row="${r}"][data-col="${c}"]`);
    if (cellEl) {
      cellEl.classList.add('drop-target');
    }
  }
}

function clearDropTargets() {
  boardEl.querySelectorAll('.drop-target').forEach((el) => el.classList.remove('drop-target'));
}

init();
