import { flipDots, getOrientations, pieceById } from './pieces.js';
import {
  canPlace,
  cloneBoard,
  findPieceAnchor,
  placePiece,
  removePiece,
} from './board.js';
import { checkWin } from './puzzle.js';

export class KanoodleGame {
  constructor(state) {
    this.state = state;
    this.selectedPieceId = null;
    this.selectedOrientationIndex = 0;
    this.listeners = new Set();
  }

  subscribe(listener) {
    this.listeners.add(listener);
    return () => this.listeners.delete(listener);
  }

  notify() {
    for (const listener of this.listeners) {
      listener(this.getSnapshot());
    }
  }

  getSnapshot() {
    return {
      ...this.state,
      board: cloneBoard(this.state.board),
      fixedPieces: new Set(this.state.fixedPieces),
      trayPieces: [...this.state.trayPieces],
      placements: { ...this.state.placements },
      selectedPieceId: this.selectedPieceId,
      selectedOrientationIndex: this.selectedOrientationIndex,
      selectedOrientation: this.getSelectedOrientation(),
    };
  }

  getSelectedOrientation() {
    if (!this.selectedPieceId) {
      return null;
    }
    const orientations = this.getOrientationsForPiece(this.selectedPieceId);
    return orientations[this.selectedOrientationIndex] || orientations[0];
  }

  getOrientationsForPiece(pieceId) {
    if (this._orientationCache?.[pieceId]) {
      return this._orientationCache[pieceId];
    }
    return getOrientations(pieceById(pieceId).dots);
  }

  setOrientationCache(cache) {
    this._orientationCache = cache;
  }

  selectPiece(pieceId) {
    if (pieceId && this.state.fixedPieces.has(pieceId) && this.isOnBoard(pieceId)) {
      return false;
    }
    this.selectedPieceId = pieceId;
    this.selectedOrientationIndex = 0;
    this.notify();
    return true;
  }

  rotateSelected(clockwise = true) {
    if (!this.selectedPieceId) {
      return;
    }
    const orientations = this.getOrientationsForPiece(this.selectedPieceId);
    const delta = clockwise ? 1 : orientations.length - 1;
    this.selectedOrientationIndex = (this.selectedOrientationIndex + delta) % orientations.length;
    this.notify();
  }

  flipSelected() {
    if (!this.selectedPieceId) {
      return;
    }
    const orientations = this.getOrientationsForPiece(this.selectedPieceId);
    const current = orientations[this.selectedOrientationIndex];
    const flipped = flipDots(current);
    const flippedKey = dotsKey(flipped);
    const matchIndex = orientations.findIndex((orientation) => dotsKey(orientation) === flippedKey);

    if (matchIndex >= 0) {
      this.selectedOrientationIndex = matchIndex;
    } else {
      this.rotateSelected();
    }
    this.notify();
  }

  isOnBoard(pieceId) {
    return this.state.board.some((row) => row.includes(pieceId));
  }

  tryPlaceAt(row, col) {
    if (!this.selectedPieceId) {
      return false;
    }

    const pieceId = this.selectedPieceId;
    if (this.state.fixedPieces.has(pieceId)) {
      return false;
    }

    const orientation = this.getSelectedOrientation();
    if (!orientation) {
      return false;
    }

    const board = this.state.board;
    const wasOnBoard = this.isOnBoard(pieceId);
    const oldPlacement = wasOnBoard ? { ...this.state.placements[pieceId] } : null;

    if (wasOnBoard) {
      removePiece(board, pieceId);
    }

    if (!canPlace(board, pieceId, orientation, row, col)) {
      if (wasOnBoard && oldPlacement?.orientation) {
        placePiece(board, pieceId, oldPlacement.orientation, oldPlacement.row, oldPlacement.col);
      }
      this.notify();
      return false;
    }

    placePiece(board, pieceId, orientation, row, col);
    this.state.placements[pieceId] = {
      row,
      col,
      orientation: orientation.map(([r, c]) => [r, c]),
      fixed: false,
    };

    if (!wasOnBoard) {
      this.state.trayPieces = this.state.trayPieces.filter((id) => id !== pieceId);
    }

    this.state.solved = checkWin(this.state);
    this.notify();
    return true;
  }

  removePieceToTray(pieceId) {
    if (this.state.fixedPieces.has(pieceId)) {
      return false;
    }
    if (!this.isOnBoard(pieceId)) {
      return false;
    }

    removePiece(this.state.board, pieceId);
    delete this.state.placements[pieceId];
    if (!this.state.trayPieces.includes(pieceId)) {
      this.state.trayPieces.push(pieceId);
    }
    this.state.solved = false;
    this.selectedPieceId = pieceId;
    this.notify();
    return true;
  }

  pickUpBoardPiece(pieceId) {
    if (this.state.fixedPieces.has(pieceId)) {
      return false;
    }

    const anchor = findPieceAnchor(this.state.board, pieceId);
    if (!anchor) {
      return false;
    }

    const placement = this.state.placements[pieceId];
    if (placement?.orientation) {
      this.selectedOrientationIndex = this.getOrientationsForPiece(pieceId).findIndex(
        (orientation) =>
          orientation
            .map(([r, c]) => `${r},${c}`)
            .sort()
            .join('|') ===
          placement.orientation
            .map(([r, c]) => `${r},${c}`)
            .sort()
            .join('|')
      );
      if (this.selectedOrientationIndex < 0) {
        this.selectedOrientationIndex = 0;
      }
    }

    removePiece(this.state.board, pieceId);
    delete this.state.placements[pieceId];
    if (!this.state.trayPieces.includes(pieceId)) {
      this.state.trayPieces.push(pieceId);
    }

    this.selectedPieceId = pieceId;
    this.state.solved = false;
    this.notify();
    return true;
  }

  resetSelection() {
    this.selectedPieceId = null;
    this.selectedOrientationIndex = 0;
    this.notify();
  }
}

function dotsKey(dots) {
  return dots
    .map(([r, c]) => `${r},${c}`)
    .sort()
    .join('|');
}
