import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import path from "node:path";
import { describe, it } from "node:test";
import { fileURLToPath } from "node:url";
import { applyNotebook, emptyMemory, loadMemory, renderMemory } from "../src/memory.js";
import { compactMemory, excerptScreen, noteRefusal } from "../src/notes.js";

const here = path.dirname(fileURLToPath(import.meta.url));

describe("durable notes", () => {
  it("keeps a claim and refuses a turn log", () => {
    assert.equal(noteRefusal("grid bugs are easy to kill"), undefined);
    assert.match(noteRefusal("after kkll, @ was on the top row") ?? "", /key trace|log of this screen/);
    assert.match(noteRefusal("n7 (life 1, turn 7) @ top row") ?? "", /turn log/);
    assert.match(noteRefusal("t14 at N wall 4 west of door") ?? "", /turn log/);
  });

  it("keeps the starter notes and drops the play diary", async () => {
    const starter = await loadMemory(path.join(here, "..", "notebook"));
    for (const note of starter.notes) {
      assert.equal(noteRefusal(note.text), undefined, note.id);
    }

    const diary = JSON.parse(
      await readFile(path.join(here, "fixtures", "play-403-notes.json"), "utf8"),
    ) as Array<{ id: string; text: string }>;
    const memory = emptyMemory();
    memory.notes = diary.map((note, index) => ({
      id: note.id,
      life: 1,
      turn: index + 1,
      text: note.text,
      retracted: false,
    }));
    memory.procedures = [
      { name: "search8", keys: "ssssssss", life: 1, turn: 1 },
      { name: "secexit", keys: "ssssssssohhokkojj", life: 1, turn: 2 },
    ];
    memory.endings = [
      {
        life: 1,
        turns: 16,
        exitReason: "turn_cap",
        screen: [
          "Rex bites the lichen.  The lichen is killed!",
          "                       ##",
          "                    ###f@      #",
          "[Runner the Stripling          ] St:15 Dx:17 Co:14 In:10 Wi:9 Ch:10 Lawful",
          "Dlvl:1 $:0 HP:18(18) Pw:1(1) AC:6 Xp:1",
        ].join("\n"),
      },
    ];
    const dropped = compactMemory(memory);
    assert.equal(dropped.droppedNotes > 50, true);
    assert.deepEqual(
      memory.notes.map((note) => note.id),
      ["n1", "n2", "n3", "n4", "n5", "n6", "n21"],
    );
    assert.deepEqual(
      memory.procedures.map((procedure) => procedure.name),
      ["search8"],
    );
    const ending = memory.endings[0]?.screen ?? "";
    assert.match(ending, /lichen is killed/);
    assert.match(ending, /Dlvl:1/);
    assert.equal(ending.includes("###f@"), false);
    assert.equal(excerptScreen(ending), ending);
  });

  it("does not put a life stamp back into the prompt", () => {
    const memory = emptyMemory();
    applyNotebook(memory, { keys: "", quit: false, note: "grid bugs are easy to kill" }, 1, 4);
    const rendered = renderMemory(memory);
    assert.match(rendered, /n1: grid bugs are easy to kill/);
    assert.equal(rendered.includes("(life "), false);
    assert.equal(rendered.includes("turn 4"), false);
  });

  it("stops a life from filing a diary, and frees a slot on retract", () => {
    const memory = emptyMemory();
    const budget = { notesAdded: 0, addedIds: [] as string[] };
    for (const text of ["letters fail while --More-- is visible", "wait is a period", "a pile can hold a web"]) {
      const acks = applyNotebook(memory, { keys: "", quit: false, note: text }, 1, 1, budget);
      assert.match(acks.join("\n"), /stored note/);
    }
    const refused = applyNotebook(
      memory,
      { keys: "l", quit: false, note: "standing next to the fungus hurt" },
      1,
      2,
      budget,
    );
    assert.match(refused.join("\n"), /already filed 3 notes/);
    assert.equal(memory.notes.length, 3);
    const first = memory.notes[0]?.id ?? "";
    const replaced = applyNotebook(
      memory,
      { keys: "", quit: false, retract: first, note: "standing next to the fungus hurt" },
      1,
      3,
      budget,
    );
    assert.match(replaced.join("\n"), /retracted/);
    assert.match(replaced.join("\n"), /stored note/);
  });
});
