/**
 * Computer-keyboard → MIDI mapping (Ableton/FL-style two octaves).
 *
 * Bottom row: Z X C V B N M , . /  (white keys starting at base octave C)
 * Mid row:    A W S E D F T G Y H U J K
 * (We use a compact subset that matches common chiptune editors.)
 */

const KEY_TO_OFFSET = {
  // Lower octave (starts at C)
  z: 0,
  s: 1,
  x: 2,
  d: 3,
  c: 4,
  v: 5,
  g: 6,
  b: 7,
  h: 8,
  n: 9,
  j: 10,
  m: 11,
  ",": 12,
  l: 13,
  ".": 14,
  ";": 15,
  "/": 16,
  // Upper octave
  q: 12,
  2: 13,
  w: 14,
  3: 15,
  e: 16,
  r: 17,
  5: 18,
  t: 19,
  6: 20,
  y: 21,
  7: 22,
  u: 23,
  i: 24,
  9: 25,
  o: 26,
  0: 27,
  p: 28,
};

/**
 * @typedef {object} KeyboardInput
 * @property {(midi: number) => void} onNoteOn
 * @property {(midi: number) => void} onNoteOff
 * @property {() => number} getBaseMidi  lowest C for the keyboard map
 * @property {() => boolean} [shouldIgnore] when true, skip (e.g. typing in input)
 */

/**
 * @param {KeyboardInput} handlers
 * @returns {{ attach: () => void, detach: () => void, held: () => number[] }}
 */
export function createKeyboardInput(handlers) {
  /** @type {Map<string, number>} */
  const heldKeys = new Map();

  /**
   * @param {KeyboardEvent} event
   */
  function onKeyDown(event) {
    if (handlers.shouldIgnore?.()) return;
    if (event.metaKey || event.ctrlKey || event.altKey) return;
    const key = event.key.length === 1 ? event.key.toLowerCase() : event.key;
    if (!(key in KEY_TO_OFFSET)) return;
    if (heldKeys.has(key)) return;
    event.preventDefault();
    const midi = handlers.getBaseMidi() + KEY_TO_OFFSET[key];
    if (midi < 0 || midi > 127) return;
    heldKeys.set(key, midi);
    handlers.onNoteOn(midi);
  }

  /**
   * @param {KeyboardEvent} event
   */
  function onKeyUp(event) {
    const key = event.key.length === 1 ? event.key.toLowerCase() : event.key;
    const midi = heldKeys.get(key);
    if (midi == null) return;
    heldKeys.delete(key);
    handlers.onNoteOff(midi);
  }

  function onBlur() {
    for (const midi of heldKeys.values()) {
      handlers.onNoteOff(midi);
    }
    heldKeys.clear();
  }

  return {
    attach() {
      window.addEventListener("keydown", onKeyDown);
      window.addEventListener("keyup", onKeyUp);
      window.addEventListener("blur", onBlur);
    },
    detach() {
      window.removeEventListener("keydown", onKeyDown);
      window.removeEventListener("keyup", onKeyUp);
      window.removeEventListener("blur", onBlur);
      onBlur();
    },
    held() {
      return [...heldKeys.values()];
    },
  };
}

export { KEY_TO_OFFSET };
