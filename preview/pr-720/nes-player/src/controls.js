// Button numbers match jsnes's Controller constants.
export const BUTTON = Object.freeze({
  A: 0,
  B: 1,
  SELECT: 2,
  START: 3,
  UP: 4,
  DOWN: 5,
  LEFT: 6,
  RIGHT: 7,
});

export const BUTTON_NAMES = [
  ["UP", "Up"],
  ["DOWN", "Down"],
  ["LEFT", "Left"],
  ["RIGHT", "Right"],
  ["B", "B"],
  ["A", "A"],
  ["SELECT", "Select"],
  ["START", "Start"],
];

// Keyed by KeyboardEvent.code, so the layout of the keyboard doesn't matter.
export const KEYS = Object.freeze({
  ArrowUp: [1, BUTTON.UP],
  ArrowDown: [1, BUTTON.DOWN],
  ArrowLeft: [1, BUTTON.LEFT],
  ArrowRight: [1, BUTTON.RIGHT],
  KeyZ: [1, BUTTON.B],
  KeyX: [1, BUTTON.A],
  ShiftRight: [1, BUTTON.SELECT],
  Enter: [1, BUTTON.START],
  KeyW: [2, BUTTON.UP],
  KeyS: [2, BUTTON.DOWN],
  KeyA: [2, BUTTON.LEFT],
  KeyD: [2, BUTTON.RIGHT],
  KeyF: [2, BUTTON.B],
  KeyG: [2, BUTTON.A],
  KeyR: [2, BUTTON.SELECT],
  KeyT: [2, BUTTON.START],
});

const KEY_LABELS = {
  ArrowUp: "↑",
  ArrowDown: "↓",
  ArrowLeft: "←",
  ArrowRight: "→",
  ShiftRight: "Right Shift",
  Enter: "Enter",
};

export function keyLabel(code) {
  return KEY_LABELS[code] ?? code.replace(/^Key/, "");
}

/** Rows of [button label, player 1 key, player 2 key] for the controls table. */
export function keyTable() {
  return BUTTON_NAMES.map(([id, label]) => {
    const keyFor = (player) =>
      Object.entries(KEYS)
        .filter(([, [p, b]]) => p === player && b === BUTTON[id])
        .map(([code]) => keyLabel(code))
        .join(", ");
    return [label, keyFor(1), keyFor(2)];
  });
}

export function keyBinding(event) {
  if (event.metaKey || event.ctrlKey || event.altKey) return null;
  return KEYS[event.code] ?? null;
}

const AXIS_THRESHOLD = 0.5;

/**
 * Reads the NES buttons held on a gamepad with the W3C standard mapping.
 * The right face button is A and the bottom one is B, as on an NES pad.
 * @param {{buttons: {pressed: boolean}[], axes: number[]}} pad
 * @returns {Set<number>}
 */
export function padButtons(pad) {
  const held = new Set();
  const pressed = (i) => Boolean(pad.buttons[i]?.pressed);
  const axis = (i) => pad.axes[i] ?? 0;
  if (pressed(1) || pressed(3)) held.add(BUTTON.A);
  if (pressed(0) || pressed(2)) held.add(BUTTON.B);
  if (pressed(8)) held.add(BUTTON.SELECT);
  if (pressed(9)) held.add(BUTTON.START);
  if (pressed(12) || axis(1) < -AXIS_THRESHOLD) held.add(BUTTON.UP);
  if (pressed(13) || axis(1) > AXIS_THRESHOLD) held.add(BUTTON.DOWN);
  if (pressed(14) || axis(0) < -AXIS_THRESHOLD) held.add(BUTTON.LEFT);
  if (pressed(15) || axis(0) > AXIS_THRESHOLD) held.add(BUTTON.RIGHT);
  return held;
}

/** The presses and releases that turn `before` into `after`. */
export function diffButtons(before, after) {
  const down = [...after].filter((b) => !before.has(b));
  const up = [...before].filter((b) => !after.has(b));
  return { down, up };
}
