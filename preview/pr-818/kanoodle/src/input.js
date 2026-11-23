export const TAP_MOVE_THRESHOLD = 12;
export const TAP_TIME_THRESHOLD = 400;
export const DRAG_START_THRESHOLD = 8;

/** True when the primary input is touch (phones, tablets). */
export function isCoarsePointer() {
  if (typeof window === 'undefined' || !window.matchMedia) {
    return false;
  }
  return window.matchMedia('(pointer: coarse)').matches;
}

/** Prefer tap-to-place when touch is the primary pointer or hover is unavailable. */
export function prefersTapPlacement() {
  if (typeof window === 'undefined' || !window.matchMedia) {
    return false;
  }
  return (
    window.matchMedia('(pointer: coarse)').matches ||
    window.matchMedia('(hover: none)').matches
  );
}

export function createPointerSession(event) {
  return {
    pointerId: event.pointerId,
    startX: event.clientX,
    startY: event.clientY,
    startTime: Date.now(),
    dragging: false,
    source: null,
    context: null,
  };
}

export function pointerMovedEnough(session, event, threshold = DRAG_START_THRESHOLD) {
  const dx = event.clientX - session.startX;
  const dy = event.clientY - session.startY;
  return Math.hypot(dx, dy) >= threshold;
}

/** True when vertical movement suggests the user is scrolling the page. */
export function isScrollGesture(session, event, threshold = DRAG_START_THRESHOLD) {
  const dx = Math.abs(event.clientX - session.startX);
  const dy = Math.abs(event.clientY - session.startY);
  return dy > dx && dy >= threshold;
}

export function isTap(session, event) {
  if (session.dragging) {
    return false;
  }
  const dx = event.clientX - session.startX;
  const dy = event.clientY - session.startY;
  const dist = Math.hypot(dx, dy);
  const elapsed = Date.now() - session.startTime;
  return dist <= TAP_MOVE_THRESHOLD && elapsed <= TAP_TIME_THRESHOLD;
}

export function cellFromPoint(x, y, root = document) {
  const el = root.elementFromPoint(x, y)?.closest('.cell');
  if (!el) {
    return null;
  }
  return {
    row: Number(el.dataset.row),
    col: Number(el.dataset.col),
    element: el,
  };
}

export function updateBodyDragState(active) {
  if (typeof document === 'undefined') {
    return;
  }
  document.body.classList.toggle('is-dragging', active);
}

export function interactionHint(prefersTap) {
  if (prefersTap) {
    return 'Tap a piece to select it, then scroll to the board and tap to place. Tap a placed piece to pick it up.';
  }
  return 'Click a piece, then drag it onto the board. Double-click a placed piece to return it.';
}
