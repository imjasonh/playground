import { ROWS, COLS, DIFFICULTY_LABELS } from './constants.js';
import { PIECES, getOrientations, pieceById, absoluteCells } from './pieces.js';
import { createGameState } from './puzzle.js';
import { listLibraryPuzzles } from './puzzleLibrary.js';
import { KanoodleGame } from './game.js';
import {
  cellFromPoint,
  createPointerSession,
  interactionHint,
  isScrollGesture,
  isTap,
  pointerMovedEnough,
  prefersTapPlacement,
  updateBodyDragState,
} from './input.js';

const orientationCache = Object.fromEntries(
  PIECES.map((piece) => [piece.id, getOrientations(piece.dots)])
);

const boardEl = document.getElementById('board');
const trayEl = document.getElementById('tray');
const statusEl = document.getElementById('status');
const hintEl = document.getElementById('interaction-hint');
const difficultyEl = document.getElementById('difficulty');
const puzzleSelectEl = document.getElementById('puzzle-select');
const newGameBtn = document.getElementById('new-game');
const rotateBtn = document.getElementById('rotate-btn');
const flipBtn = document.getElementById('flip-btn');
const returnBtn = document.getElementById('return-btn');
const selectedPreviewEl = document.getElementById('selected-preview');
const previewShapeEl = document.getElementById('preview-shape');
const ghostLayerEl = document.getElementById('ghost-layer');

let game = null;
let pointerSession = null;
let tapMode = prefersTapPlacement();

function init() {
  document.body.classList.toggle('touch-mode', tapMode);
  if (tapMode) {
    document.querySelector('.settings-panel')?.removeAttribute('open');
  }
  if (hintEl) {
    hintEl.textContent = interactionHint(tapMode);
  }

  populatePuzzleSelect();
  bindControls();
  bindGlobalPointerHandlers();
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
  returnBtn.addEventListener('click', () => returnSelectedPiece());

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

  window.matchMedia('(pointer: coarse)').addEventListener('change', () => {
    tapMode = prefersTapPlacement();
    document.body.classList.toggle('touch-mode', tapMode);
    if (hintEl) {
      hintEl.textContent = interactionHint(tapMode);
    }
  });
}

function bindGlobalPointerHandlers() {
  document.addEventListener('pointermove', onPointerMove);
  document.addEventListener('pointerup', onPointerUp);
  document.addEventListener('pointercancel', onPointerUp);
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

function returnSelectedPiece() {
  if (!game?.selectedPieceId) {
    return;
  }
  const pieceId = game.selectedPieceId;
  if (game.state.fixedPieces.has(pieceId)) {
    return;
  }
  if (game.isOnBoard(pieceId)) {
    game.pickUpBoardPiece(pieceId);
  } else {
    game.resetSelection();
  }
}

function render(snapshot) {
  renderBoard(snapshot);
  renderTray(snapshot);
  renderStatus(snapshot);
  renderSelectedPreview(snapshot);
  updateActionButtons(snapshot);
}

function updateActionButtons(snapshot) {
  const hasSelection = Boolean(snapshot.selectedPieceId);
  rotateBtn.disabled = !hasSelection;
  flipBtn.disabled = !hasSelection;

  const canReturn =
    hasSelection &&
    !snapshot.fixedPieces.has(snapshot.selectedPieceId) &&
    (snapshot.trayPieces.includes(snapshot.selectedPieceId) ||
      snapshot.board.some((row) => row.includes(snapshot.selectedPieceId)));

  returnBtn.disabled = !canReturn;
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
  const selected = snapshot.selectedPieceId ? ` Selected: ${snapshot.selectedPieceId}.` : '';
  statusEl.textContent = `${difficultyLabel} — ${remaining} piece${remaining === 1 ? '' : 's'} left.${selected}`;
}

function renderBoard(snapshot) {
  boardEl.innerHTML = '';

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

        if (!tapMode) {
          cell.addEventListener('dblclick', () => {
            if (!snapshot.fixedPieces.has(pieceId)) {
              game.pickUpBoardPiece(pieceId);
            }
          });
        }
      } else {
        cell.classList.add('empty');
      }

      cell.addEventListener('pointerdown', (event) => onBoardPointerDown(event, row, col, pieceId));
      boardEl.appendChild(cell);
    }
  }

  if (!pointerSession?.dragging) {
    ghostLayerEl.innerHTML = '';
    clearDropTargets();
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
    const item = document.createElement('button');
    item.type = 'button';
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
    item.appendChild(buildShapeElement(orientation, piece.color, tapMode ? 16 : 14));

    item.addEventListener('pointerdown', (event) => onTrayPointerDown(event, pieceId));

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
  previewShapeEl.appendChild(buildShapeElement(snapshot.selectedOrientation, piece.color, 20));
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

function onTrayPointerDown(event, pieceId) {
  if (event.button !== 0 && event.pointerType !== 'touch') {
    return;
  }

  if (!tapMode) {
    event.preventDefault();
    boardEl.setPointerCapture?.(event.pointerId);
  }

  pointerSession = createPointerSession(event);
  pointerSession.source = 'tray';
  pointerSession.context = { pieceId };
}

function onBoardPointerDown(event, row, col, pieceId) {
  if (event.button !== 0 && event.pointerType !== 'touch') {
    return;
  }

  if (!tapMode) {
    event.preventDefault();
    boardEl.setPointerCapture(event.pointerId);
  }

  pointerSession = createPointerSession(event);
  pointerSession.source = 'board';
  pointerSession.context = { row, col, pieceId };
}

function onPointerMove(event) {
  if (!pointerSession || event.pointerId !== pointerSession.pointerId) {
    return;
  }

  if (!pointerSession.dragging) {
    if (tapMode && isScrollGesture(pointerSession, event)) {
      pointerSession = null;
      return;
    }
    if (pointerMovedEnough(pointerSession, event)) {
      beginDrag(event);
    }
    return;
  }

  event.preventDefault();
  const cell = cellFromPoint(event.clientX, event.clientY);
  if (cell) {
    showGhost(pointerSession.context.pieceId ?? game.getSnapshot().selectedPieceId, cell.row, cell.col);
    highlightDropTarget(cell.row, cell.col);
  }
}

function beginDrag(event) {
  pointerSession.dragging = true;
  updateBodyDragState(true);
  boardEl.setPointerCapture?.(event.pointerId);
  if (tapMode) {
    event.preventDefault();
  }

  const { source, context } = pointerSession;
  if (source === 'tray') {
    game.selectPiece(context.pieceId);
  } else if (source === 'board') {
    const snapshot = game.getSnapshot();
    const { pieceId, row, col } = context;
    if (pieceId && !snapshot.fixedPieces.has(pieceId)) {
      game.pickUpBoardPiece(pieceId);
    } else if (snapshot.selectedPieceId) {
      pointerSession.context.pieceId = snapshot.selectedPieceId;
    } else {
      pointerSession.dragging = false;
      updateBodyDragState(false);
    }
  }

  const pieceId = pointerSession.context.pieceId ?? game.getSnapshot().selectedPieceId;
  if (pieceId && pointerSession.dragging) {
    const cell = cellFromPoint(pointerSession.startX, pointerSession.startY);
    showGhost(pieceId, cell?.row ?? 0, cell?.col ?? 0);
  }
}

function onPointerUp(event) {
  if (!pointerSession || event.pointerId !== pointerSession.pointerId) {
    return;
  }

  boardEl.releasePointerCapture?.(event.pointerId);

  const session = pointerSession;
  pointerSession = null;

  if (session.dragging) {
    finishDrag(event);
    return;
  }

  if (isTap(session, event)) {
    handleTap(session, event);
  }

  ghostLayerEl.innerHTML = '';
  clearDropTargets();
  updateBodyDragState(false);
}

function handleTap(session, event) {
  const snapshot = game.getSnapshot();

  if (session.source === 'tray') {
    game.selectPiece(session.context.pieceId);
    return;
  }

  const cell = cellFromPoint(event.clientX, event.clientY) ?? session.context;
  const { row, col, pieceId } = cell.row !== undefined ? cell : session.context;

  if (pieceId && !snapshot.fixedPieces.has(pieceId)) {
    game.pickUpBoardPiece(pieceId);
    return;
  }

  if (snapshot.selectedPieceId) {
    game.tryPlaceCovering(row, col);
  }
}

function finishDrag(event) {
  const cell = cellFromPoint(event.clientX, event.clientY);
  if (cell) {
    const pieceId = game.getSnapshot().selectedPieceId;
    if (pieceId) {
      game.selectPiece(pieceId);
      game.tryPlaceCovering(cell.row, cell.col);
    }
  }

  ghostLayerEl.innerHTML = '';
  clearDropTargets();
  updateBodyDragState(false);
}

function showGhost(pieceId, row, col) {
  if (!pieceId) {
    return;
  }

  const snapshot = game.getSnapshot();
  const orientation = snapshot.selectedOrientation || orientationCache[pieceId][0];
  const piece = pieceById(pieceId);
  const cells = absoluteCells(orientation, row, col);

  ghostLayerEl.hidden = false;
  ghostLayerEl.innerHTML = '';

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
    dot.className = 'piece-dot ghost-dot';
    dot.style.backgroundColor = piece.color;
    dot.style.width = `${rect.width}px`;
    dot.style.height = `${rect.height}px`;
    dot.style.left = `${rect.left - wrapRect.left}px`;
    dot.style.top = `${rect.top - wrapRect.top}px`;
    ghostLayerEl.appendChild(dot);
  }
}

function highlightDropTarget(row, col) {
  const snapshot = game.getSnapshot();
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
