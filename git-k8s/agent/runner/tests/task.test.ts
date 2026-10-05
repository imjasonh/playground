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
  workTree: "/src",
  diffFile: "/input/change.diff",
  logFile: "/input/log.txt",
  filesFile: "/input/files",
  keyFile: "/key/api-key",
  resultFile: "/result/result.json",
  terminationLog: "/dev/termination-log",
};

const merge: Task = {
  ...valid,
  edit: true,
  tools: ["read", "edit"],
  base: "fedcba9876543210fedcba9876543210fedcba98",
  mergeName: "main",
  mergeHead: "1111111111111111111111111111111111111111",
  conflictsFile: "/input/conflicts",
  mergeLogFile: "/input/merge-log.txt",
  mergeDiffFile: "/input/merge.diff",
  mergeChangesFile: "/input/merge-changes",
};

test("parses a task", () => {
  assert.deepEqual(parseTask(JSON.stringify(valid)), valid);
  const full = { ...valid, changesFile: "/input/changes" };
  assert.deepEqual(parseTask(JSON.stringify(full)), full);
  assert.deepEqual(parseTask(JSON.stringify(merge)), merge);
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
    [JSON.stringify({ ...valid, changesFile: 7 }), /changesFile must be a string/],
    [JSON.stringify({ ...valid, instructions: "" }), /instructions can't be empty/],
    [JSON.stringify({ ...valid, tools: "read" }), /tools must be a list of tool names/],
    [JSON.stringify({ ...valid, tools: [] }), /tools must be a list of tool names/],
    [JSON.stringify({ ...valid, tools: ["read", "shell"] }), /tools can hold only read, grep, glob, ls, edit, delete/],
    [JSON.stringify({ ...valid, tools: [7] }), /tools can hold only/],
    [JSON.stringify({ ...valid, tools: ["read", "edit"] }), /tools can't hold edit unless the task edits files/],
    [JSON.stringify({ ...merge, base: "" }), /base can't be empty in a merge/],
    [JSON.stringify({ ...merge, mergeHead: "" }), /mergeHead can't be empty in a merge/],
    [JSON.stringify({ ...merge, conflictsFile: undefined }), /conflictsFile can't be empty in a merge/],
    [JSON.stringify({ ...merge, mergeDiffFile: undefined }), /mergeDiffFile can't be empty in a merge/],
    [JSON.stringify({ ...merge, mergeChangesFile: "" }), /mergeChangesFile can't be empty in a merge/],
    [JSON.stringify({ ...merge, mergeDiffFile: 7 }), /mergeDiffFile must be a string/],
    [JSON.stringify({ ...merge, mergeName: 7 }), /mergeName must be a string/],
    [JSON.stringify({ ...merge, mergeName: "" }), /mergeName can't be empty in a merge/],
  ];
  for (const [json, want] of cases) {
    assert.throws(() => parseTask(json), want, json);
  }
});
