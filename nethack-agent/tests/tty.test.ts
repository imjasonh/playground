import assert from "node:assert/strict";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { describe, it } from "node:test";
import { createTtyBackend } from "../src/games/tty.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const fixture = path.join(here, "fixtures", "line_game.py");

describe("tty backend", () => {
  it("shows a screen and sends keys to a child process", async () => {
    const game = await createTtyBackend({
      command: "python3",
      args: [fixture],
      idleMs: 40,
      startTimeoutMs: 3000,
      cols: 40,
      rows: 8,
    }).start({ lifeDir: path.join(here, "..", ".workspaces", "tty-test"), seed: 1 });
    try {
      const first = await game.observe();
      assert.match(first.screen, /@\./);
      const moved = await game.sendKeys("l");
      assert.match(moved.screen, /\.@/);
      const done = await game.sendKeys("x");
      assert.match(done.screen, /BYE/);
      assert.equal(done.ended, true);
    } finally {
      await game.close();
    }
  });
});
