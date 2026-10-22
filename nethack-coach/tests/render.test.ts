import assert from "node:assert/strict";
import { test } from "node:test";
import { layoutSidebar, wrapText } from "../src/render.js";
import type { SidebarView } from "../src/types.js";

test("wrap keeps words whole within the width", () => {
  assert.deepEqual(wrapText("the quick brown fox", 9), ["the quick", "brown fox"]);
});

test("wrap preserves blank lines from the source", () => {
  assert.deepEqual(wrapText("a\n\nb", 10), ["a", "", "b"]);
});

test("wrap hard-splits a word longer than the width", () => {
  assert.deepEqual(wrapText("abcdefgh", 3), ["abc", "def", "gh"]);
});

test("every laid-out line fits the pane width", () => {
  const view: SidebarView = {
    status: "watching",
    auto: true,
    advice: "Your HP is low. Pray for help by pressing #pray then confirming.",
    tokens: 1234,
    costCents: 42,
  };
  const width = 24;
  for (const line of layoutSidebar(view, width)) {
    assert.ok(line.length <= width, `line too wide: ${JSON.stringify(line)}`);
  }
});

test("the footer shows auto state and cost when known", () => {
  const view: SidebarView = { status: "paused", auto: false, advice: "x", tokens: 1000, costCents: 150 };
  const text = layoutSidebar(view, 40).join("\n");
  assert.match(text, /auto off/);
  assert.match(text, /\$1\.50/);
  assert.match(text, /1,000 tokens/);
});
