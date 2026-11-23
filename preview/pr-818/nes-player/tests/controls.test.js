import test from "node:test";
import assert from "node:assert/strict";

import {
  BUTTON,
  KEYS,
  diffButtons,
  keyBinding,
  keyTable,
  padButtons,
} from "../src/controls.js";

test("each player has one key for each of the eight buttons", () => {
  for (const player of [1, 2]) {
    const buttons = Object.values(KEYS)
      .filter(([p]) => p === player)
      .map(([, b]) => b)
      .sort();
    assert.deepEqual(buttons, [0, 1, 2, 3, 4, 5, 6, 7]);
  }
});

test("keyBinding maps by code and ignores shortcuts", () => {
  assert.deepEqual(keyBinding({ code: "KeyX" }), [1, BUTTON.A]);
  assert.deepEqual(keyBinding({ code: "KeyT" }), [2, BUTTON.START]);
  assert.equal(keyBinding({ code: "KeyR", metaKey: true }), null);
  assert.equal(keyBinding({ code: "KeyR", ctrlKey: true }), null);
  assert.equal(keyBinding({ code: "KeyQ" }), null);
});

test("keyTable lists both players' keys for each button", () => {
  const rows = keyTable();
  assert.equal(rows.length, 8);
  assert.deepEqual(rows[0], ["Up", "↑", "W"]);
  assert.deepEqual(
    rows.find(([b]) => b === "Start"),
    ["Start", "Enter", "T"],
  );
});

function pad(pressed = [], axes = [0, 0]) {
  return {
    buttons: Array.from({ length: 17 }, (_, i) => ({ pressed: pressed.includes(i) })),
    axes,
  };
}

test("padButtons reads the standard mapping", () => {
  assert.deepEqual(padButtons(pad([1, 9, 12])), new Set([BUTTON.A, BUTTON.START, BUTTON.UP]));
  assert.deepEqual(padButtons(pad([0, 8, 15])), new Set([BUTTON.B, BUTTON.SELECT, BUTTON.RIGHT]));
  assert.deepEqual(padButtons(pad([], [-0.9, 0.8])), new Set([BUTTON.LEFT, BUTTON.DOWN]));
  assert.deepEqual(padButtons(pad([], [0.3, -0.3])), new Set());
});

test("padButtons tolerates a pad with few buttons", () => {
  assert.deepEqual(padButtons({ buttons: [{ pressed: true }], axes: [] }), new Set([BUTTON.B]));
});

test("diffButtons reports presses and releases", () => {
  const { down, up } = diffButtons(new Set([BUTTON.A, BUTTON.UP]), new Set([BUTTON.UP, BUTTON.B]));
  assert.deepEqual(down, [BUTTON.B]);
  assert.deepEqual(up, [BUTTON.A]);
});
