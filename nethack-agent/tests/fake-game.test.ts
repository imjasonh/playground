import assert from "node:assert/strict";
import { describe, it } from "node:test";
import { createFakeBackend } from "../src/games/fake.js";

describe("fake game", () => {
  it("moves the mark when sent a movement byte", async () => {
    const game = await createFakeBackend().start({ lifeDir: "/tmp", seed: 1 });
    const before = await game.observe();
    assert.match(before.screen, /#@/);
    const after = await game.sendKeys("l");
    assert.match(after.screen, /#\.@/);
    assert.equal(after.ended, false);
  });

  it("ends when the mark lands on the caret", async () => {
    const game = await createFakeBackend().start({ lifeDir: "/tmp", seed: 1 });
    const after = await game.sendKeys("lllljj");
    assert.equal(after.ended, true);
    assert.match(after.screen, /You die\./);
  });

  it("ends with a different screen when the angle key is sent on the angle tile", async () => {
    const game = await createFakeBackend().start({ lifeDir: "/tmp", seed: 1 });
    const moved = await game.sendKeys("lllllllljj");
    assert.equal(moved.ended, false);
    const done = await game.sendKeys(">");
    assert.equal(done.ended, true);
    assert.match(done.screen, /You ascend\./);
  });
});
