import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { existsSync, lstatSync, readFileSync, symlinkSync, unlinkSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { test } from "node:test";
import { fakeBackend } from "../src/backends/fake.js";
import type { AgentRequest, Backend } from "../src/backends/types.js";
import { MAX_DIFF, MAX_LOG } from "../src/prompt.js";
import type { Result } from "../src/result.js";
import { runFromEnv, type RunOptions } from "../src/run.js";
import type { Task } from "../src/task.js";
import { MAX_PATHS } from "../src/touched.js";
import { prepareMerge, preparePod } from "./pod.js";

const quiet: RunOptions = { log: () => undefined };

async function runTask(task: Task, options: RunOptions = quiet): Promise<number> {
  return runFromEnv({ AGENT_TASK: JSON.stringify(task) }, options);
}

function readResult(task: Task): Result {
  return JSON.parse(readFileSync(task.resultFile, "utf8")) as Result;
}

test("fails a change that adds the marker, and reports where", async () => {
  const task = preparePod({ "a.txt": "one\n" }, { "a.txt": "one\ntwo DO NOT MERGE\n" });
  assert.equal(await runTask(task), 0);

  const result = readResult(task);
  assert.equal(result.verdict, "fail");
  assert.equal(result.summary, "1 added line holds DO NOT MERGE");
  assert.equal(result.reasoning, "The change adds DO NOT MERGE at a.txt:2.");
  assert.equal(result.model, "fake:composer-2.5");
  assert.ok(result.usage.inputTokens > 0 && result.usage.outputTokens > 0);
  assert.equal(result.costCents, undefined);
  assert.deepEqual(result.files, []);

  const digest = createHash("sha256").update(readFileSync(task.resultFile)).digest("hex");
  assert.equal(readFileSync(task.terminationLog, "utf8"), `sha256:${digest}`);
  assert.equal(existsSync(task.keyFile), false, "the runner deletes the key file");
});

test("passes a clean change", async () => {
  const task = preparePod({ "a.txt": "one\n" }, { "b.txt": "fine\n" });
  assert.equal(await runTask(task), 0);
  assert.equal(readResult(task).verdict, "pass");
});

test("reads only the start of a long diff and commit log", async () => {
  const task = preparePod({}, { "a.txt": "a\n" });
  writeFileSync(task.diffFile, `diff --git a/a.txt b/a.txt\n--- a/a.txt\n+++ b/a.txt\n@@ -1 +1,100001 @@\n${"+x\n".repeat(100_000)}+DO NOT MERGE\n`);
  writeFileSync(task.logFile, `abc1234 ${"x".repeat(100)}\n`.repeat(2 * MAX_LOG));
  let request: AgentRequest | undefined;
  const capture: Backend = async (r) => {
    request = r;
    return fakeBackend(r);
  };
  assert.equal(await runTask(task, { ...quiet, backends: { fake: capture } }), 0);
  assert.equal(readResult(task).verdict, "pass", "the marker is past the part of the diff that the agent sees");
  assert.ok(request);
  assert.ok(Buffer.byteLength(request.diff) <= MAX_DIFF && request.diff.endsWith("+x\n"));
  assert.ok(request.prompt.length < MAX_DIFF + MAX_LOG + 5000);
  assert.match(request.prompt, /longer than 200000 bytes/);
});

test("lists every path that the change touches, and hides no files", async () => {
  const task = preparePod({ ".cursorignore": "", "a.txt": "a\n" }, { ".cursorignore": "secret/\n", "secret/x.txt": "x\n" });
  assert.equal(existsSync(join(task.workTree, ".cursorignore")), false);
  assert.equal(readFileSync(join(task.workTree, "secret", "x.txt"), "utf8"), "x\n");
  let prompt = "";
  const capture: Backend = async (r) => {
    prompt = r.prompt;
    return fakeBackend(r);
  };
  assert.equal(await runTask(task, { ...quiet, backends: { fake: capture } }), 0);
  assert.match(prompt, /changed type\):\n\nM \.cursorignore\nA secret\/x\.txt\n\n/);
});

test("refuses a change that touches too many paths", async (t) => {
  t.mock.method(console, "error", () => undefined);
  const task = preparePod({}, { "a.txt": "a\n" });
  writeFileSync(task.changesFile ?? "", "A\0a.txt\0".repeat(MAX_PATHS + 1));
  assert.equal(await runTask(task), 1);
  assert.equal(readFileSync(task.terminationLog, "utf8"), "the change touches more than 1000 paths, more than an agent can check");
});

test("reports the files that the agent changed", async () => {
  const task = preparePod(
    { "a.txt": "one\n", "keep.txt": "keep\n" },
    { "a.txt": "one\ntwo DO NOT MERGE\nthree\n", "new.txt": "DO NOT MERGE\n" },
    { edit: true },
  );
  assert.equal(await runTask(task), 0);

  const result = readResult(task);
  assert.equal(result.verdict, "fail");
  assert.match(result.reasoning, /a\.txt:2, new\.txt:1\. The fake agent deleted those lines\.$/);
  assert.deepEqual(
    result.files.map((f) => [f.path, f.mode, Buffer.from(f.content ?? "", "base64").toString()]),
    [
      ["a.txt", "100644", "one\nthree\n"],
      ["new.txt", "100644", ""],
    ],
  );
});

test("resolves a merge, and reports the files of the merge that the agent changed", async () => {
  const task = prepareMerge(
    { "a.txt": "one\ntwo\nthree\n", "keep.txt": "keep\n" },
    { "a.txt": "one\nours\nthree\n" },
    { "a.txt": "one\ntheirs\nthree\n", "new.txt": "new\n" },
    { edit: true, tools: ["read", "edit"] },
  );
  const conflict = `one\n<<<<<<< ${task.head}\nours\n||||||| ${task.base}\ntwo\n=======\ntheirs\n>>>>>>> ${task.mergeHead}\nthree\n`;
  assert.equal(readFileSync(join(task.workTree, "a.txt"), "utf8"), conflict);
  assert.equal(readFileSync(join(task.workTree, "new.txt"), "utf8"), "new\n");
  let request: AgentRequest | undefined;
  const resolve: Backend = async (r) => {
    request = r;
    writeFileSync(join(r.cwd, "a.txt"), "one\nours and theirs\nthree\n");
    return {
      text: '{"verdict": "pass", "summary": "merged"}',
      model: r.model,
      usage: { inputTokens: 1, outputTokens: 1, cacheReadTokens: 0, cacheWriteTokens: 0 },
    };
  };
  assert.equal(await runTask(task, { ...quiet, backends: { fake: resolve } }), 0);
  assert.ok(request);
  assert.deepEqual(request.tools, ["read", "edit"]);
  assert.match(request.prompt, /\nThe paths that conflict:\n\na\.txt\n\n/);
  assert.match(request.prompt, /\nThe merged branch's commits since the merge base, newest first:\n\n[0-9a-f]+ Theirs\n\n/);
  assert.deepEqual(
    readResult(task).files.map((f) => [f.path, Buffer.from(f.content ?? "", "base64").toString()]),
    [["a.txt", "one\nours and theirs\nthree\n"]],
  );
});

test("offers the tools that the task allows", async () => {
  const tools: (string[] | undefined)[] = [];
  const capture: Backend = async (r) => {
    tools.push(r.tools);
    return fakeBackend(r);
  };
  for (const edit of [false, true]) {
    assert.equal(await runTask(preparePod({}, { "a.txt": "a\n" }, { edit }), { ...quiet, backends: { fake: capture } }), 0);
  }
  assert.deepEqual(tools, [
    ["read", "grep", "glob", "ls"],
    ["read", "grep", "glob", "ls", "edit", "delete"],
  ]);
});

test("won't edit a tree with a path that isn't UTF-8", async (t) => {
  t.mock.method(console, "error", () => undefined);
  const task = preparePod({ "a.txt": "a\n" }, {}, { edit: true });
  const record = Buffer.from("100644 ce013625030ba8dba906f756967f9e9ca394464a 0\tb\xff\0", "latin1");
  writeFileSync(task.filesFile, Buffer.concat([readFileSync(task.filesFile), record]));
  let ran = false;
  const agent: Backend = async (r) => {
    ran = true;
    return fakeBackend(r);
  };
  assert.equal(await runTask(task, { ...quiet, backends: { fake: agent } }), 1);
  assert.equal(ran, false);
  assert.match(readFileSync(task.terminationLog, "utf8"), /the path "b\uFFFD" isn't valid UTF-8/);
});

test("reports no files when the agent changes none", async () => {
  const task = preparePod({ "a.txt": "one\n" }, { "a.txt": "two\n" }, { edit: true });
  assert.equal(await runTask(task), 0);
  assert.deepEqual(readResult(task).files, []);
});

test("needs an API key for the cursor backend", async (t) => {
  t.mock.method(console, "error", () => undefined);
  const task = preparePod({}, { "a.txt": "a\n" }, { backend: "cursor" });
  unlinkSync(task.keyFile);
  assert.equal(await runTask(task), 1);
  assert.match(readFileSync(task.terminationLog, "utf8"), /holds no Cursor API key/);
  assert.equal(existsSync(task.resultFile), false);
});

test("keeps the API key out of error messages", async (t) => {
  t.mock.method(console, "error", () => undefined);
  const leaky: Backend = async (request) => {
    throw new Error(`can't use ${request.apiKey}`);
  };
  const task = preparePod({}, { "a.txt": "a\n" });
  assert.equal(await runTask(task, { ...quiet, backends: { fake: leaky } }), 1);
  assert.equal(readFileSync(task.terminationLog, "utf8"), "can't use [REDACTED]");
});

test("keeps the API key out of the answer", async () => {
  const leaky: Backend = async (request) => ({
    text: JSON.stringify({ verdict: "pass", summary: `key ${request.apiKey}`, reasoning: request.apiKey }),
    model: request.model,
    usage: { inputTokens: 1, outputTokens: 1, cacheReadTokens: 0, cacheWriteTokens: 0 },
  });
  const task = preparePod({}, { "a.txt": "a\n" });
  assert.equal(await runTask(task, { ...quiet, backends: { fake: leaky } }), 0);
  const result = readResult(task);
  assert.equal(result.summary, "key [REDACTED]");
  assert.equal(result.reasoning, "[REDACTED]");
});

test("refuses files that hold the API key", async (t) => {
  t.mock.method(console, "error", () => undefined);
  const leaky: Backend = async (request) => {
    writeFileSync(join(request.cwd, "a.txt"), `key=${request.apiKey}\n`);
    return {
      text: '{"verdict": "pass", "summary": "ok"}',
      model: request.model,
      usage: { inputTokens: 1, outputTokens: 1, cacheReadTokens: 0, cacheWriteTokens: 0 },
    };
  };
  const task = preparePod({}, { "a.txt": "a\n" }, { edit: true });
  assert.equal(await runTask(task, { ...quiet, backends: { fake: leaky } }), 1);
  assert.equal(readFileSync(task.terminationLog, "utf8"), "the agent wrote the Cursor API key to a.txt");
  assert.equal(existsSync(task.resultFile), false);
});

test("fails an answer without a verdict", async (t) => {
  t.mock.method(console, "error", () => undefined);
  const vague: Backend = async (request) => ({
    text: "Looks fine to me.",
    model: request.model,
    usage: { inputTokens: 1, outputTokens: 1, cacheReadTokens: 0, cacheWriteTokens: 0 },
  });
  const task = preparePod({}, { "a.txt": "a\n" });
  assert.equal(await runTask(task, { ...quiet, backends: { fake: vague } }), 1);
  assert.match(readFileSync(task.terminationLog, "utf8"), /doesn't end with a JSON verdict: "Looks fine to me\."/);
});

test("replaces a link at the result path instead of following it", async () => {
  const task = preparePod({}, { "a.txt": "a\n" });
  const outside = join(task.resultFile, "..", "..", "outside.txt");
  writeFileSync(outside, "original");
  symlinkSync(outside, task.resultFile);
  assert.equal(await runTask(task), 0);
  assert.equal(readFileSync(outside, "utf8"), "original");
  assert.ok(lstatSync(task.resultFile).isFile());
  assert.equal(readResult(task).verdict, "pass");
});

test("rejects a task that isn't valid", async (t) => {
  t.mock.method(console, "error", () => undefined);
  assert.equal(await runFromEnv({}, quiet), 1);
  assert.equal(await runFromEnv({ AGENT_TASK: "{}" }, quiet), 1);
});
