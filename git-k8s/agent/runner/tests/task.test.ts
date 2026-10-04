import assert from "node:assert/strict";
import { test } from "node:test";
import { parseTask, type Task } from "../src/task.js";

const valid: Task = {
  backend: "fake",
  model: "composer-2.5",
  instructions: "Review the change.",
  edit: false,
  timeoutSeconds: 900,
  branch: "c/x",
  parent: "main",
  head: "0123456789abcdef0123456789abcdef01234567",
  base: "",
  workTree: "/src/repo",
  diffFile: "/input/change.diff",
  logFile: "/input/log.txt",
  filesFile: "/input/files",
  keyFile: "/key/api-key",
  resultFile: "/result/result.json",
  terminationLog: "/dev/termination-log",
};

test("parses a task", () => {
  assert.deepEqual(parseTask(JSON.stringify(valid)), valid);
});

test("rejects tasks that aren't valid", () => {
  const cases: [string, RegExp][] = [
    ["", /isn't valid JSON/],
    ["[]", /isn't a JSON object/],
    [JSON.stringify({ ...valid, backend: "openai" }), /backend must be one of cursor, fake/],
    [JSON.stringify({ ...valid, edit: "yes" }), /edit must be a boolean/],
    [JSON.stringify({ ...valid, timeoutSeconds: 0 }), /timeoutSeconds must be a positive integer/],
    [JSON.stringify({ ...valid, timeoutSeconds: 1.5 }), /timeoutSeconds must be a positive integer/],
    [JSON.stringify({ ...valid, head: 7 }), /head must be a string/],
    [JSON.stringify({ ...valid, instructions: "" }), /instructions can't be empty/],
  ];
  for (const [json, want] of cases) {
    assert.throws(() => parseTask(json), want, json);
  }
});
