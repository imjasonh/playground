import assert from "node:assert/strict";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { describe, it } from "node:test";
import { runSession } from "../src/harness.js";
import { loadMemory } from "../src/memory.js";
import { assertLearningGame } from "../src/real-game.js";

const here = path.dirname(fileURLToPath(import.meta.url));

describe("learning target", () => {
  it("refuses to keep notes from the fake screen", () => {
    assert.throws(() => assertLearningGame("fake"), /nethack process/);
  });

  it("loads the starter notes from a real nethack session", async () => {
    const memory = await loadMemory(path.join(here, "..", "notebook"));
    assert.equal(memory.notes.filter((note) => !note.retracted).length, 6);
    assert.equal(memory.nextNote, 7);
    assert.match(memory.notes[0]?.text ?? "", /Shall I pick character's race/);
  });

  it("refuses a notebook directory on a fake run", async () => {
    await assert.rejects(
      () =>
        runSession({
          backend: "mock",
          game: "fake",
          model: "mock",
          lives: 1,
          maxTurns: 1,
          seed: 1,
          resultsDir: "/tmp/nethack-agent-fake-results",
          workspacesRoot: "/tmp/nethack-agent-fake-ws",
          notebookDir: "/tmp/nethack-agent-fake-notebook",
          dryRun: true,
        }),
      /nethack process/,
    );
  });
});
