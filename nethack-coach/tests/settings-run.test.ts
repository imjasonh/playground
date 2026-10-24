import assert from "node:assert/strict";
import { mkdtemp, readFile, readdir, writeFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { test } from "node:test";
import { RC_BEGIN, RC_END } from "../src/prompts.js";
import { runSettings, type SettingsDeps } from "../src/settings-run.js";
import type { Advisor } from "../src/types.js";

function fakeAdvisor(config?: string): () => Promise<Advisor> {
  const block = config ? `\n${RC_BEGIN}\n${config}\n${RC_END}\n` : "";
  let sawPrompt = "";
  const advisor: Advisor = {
    async advise(prompt: string) {
      sawPrompt = prompt;
      return { text: `Here is my review.${block}`, usage: { inputTokens: 100, outputTokens: 40, totalTokens: 140 } };
    },
    async getBilledUsage() {
      return { usage: { inputTokens: 0, outputTokens: 0, totalTokens: 0 }, rawCostCents: 11 };
    },
    async dispose() {},
  };
  const make = async () => advisor;
  (make as unknown as { seen: () => string }).seen = () => sawPrompt;
  return make;
}

function deps(over: Partial<SettingsDeps> & Pick<SettingsDeps, "makeAdvisor" | "home">): SettingsDeps {
  return {
    now: () => new Date("2026-10-22T20:30:00.000Z"),
    log: () => {},
    ...over,
  };
}

test("print-only leaves the existing file untouched", async () => {
  const dir = await mkdtemp(path.join(os.tmpdir(), "nhc-set-"));
  const rc = path.join(dir, ".nethackrc");
  await writeFile(rc, "OPTIONS=color\n");
  const result = await runSettings(
    { file: rc, write: false },
    deps({ makeAdvisor: fakeAdvisor("OPTIONS=color\nOPTIONS=!autopickup"), home: dir }),
  );
  assert.equal(result.wrote, undefined);
  assert.equal(await readFile(rc, "utf8"), "OPTIONS=color\n");
  assert.equal(result.costCents, 11);
  assert.equal(result.tokens, 140);
});

test("--write backs up the original and saves the suggestion", async () => {
  const dir = await mkdtemp(path.join(os.tmpdir(), "nhc-set-"));
  const rc = path.join(dir, ".nethackrc");
  await writeFile(rc, "OPTIONS=color\n");
  const result = await runSettings(
    { file: rc, write: true },
    deps({ makeAdvisor: fakeAdvisor("OPTIONS=color\nOPTIONS=!autopickup"), home: dir }),
  );
  assert.equal(result.wrote, rc);
  assert.equal(await readFile(rc, "utf8"), "OPTIONS=color\nOPTIONS=!autopickup\n");
  assert.ok(result.backup && existsSync(result.backup));
  assert.equal(await readFile(result.backup, "utf8"), "OPTIONS=color\n");
});

test("--output writes a new file and never backs up the original", async () => {
  const dir = await mkdtemp(path.join(os.tmpdir(), "nhc-set-"));
  const rc = path.join(dir, ".nethackrc");
  await writeFile(rc, "OPTIONS=color\n");
  const out = path.join(dir, "suggested.rc");
  const result = await runSettings(
    { file: rc, write: false, output: out },
    deps({ makeAdvisor: fakeAdvisor("OPTIONS=!autopickup"), home: dir }),
  );
  assert.equal(result.wrote, out);
  assert.equal(result.backup, undefined);
  assert.equal(await readFile(out, "utf8"), "OPTIONS=!autopickup\n");
  assert.equal(await readFile(rc, "utf8"), "OPTIONS=color\n");
});

test("with no config present it drafts one and reads nothing", async () => {
  const dir = await mkdtemp(path.join(os.tmpdir(), "nhc-set-"));
  const out = path.join(dir, "fresh.rc");
  const result = await runSettings(
    { write: false, output: out },
    deps({ makeAdvisor: fakeAdvisor("OPTIONS=color"), home: dir, nethackoptions: undefined }),
  );
  assert.equal(await readFile(out, "utf8"), "OPTIONS=color\n");
  // No ~/.nethackrc existed, so no backup was taken.
  assert.equal((await readdir(dir)).filter((f) => f.includes(".bak")).length, 0);
});

test("asking to write without a returned block is an error", async () => {
  const dir = await mkdtemp(path.join(os.tmpdir(), "nhc-set-"));
  const rc = path.join(dir, ".nethackrc");
  await writeFile(rc, "OPTIONS=color\n");
  await assert.rejects(
    runSettings({ file: rc, write: true }, deps({ makeAdvisor: fakeAdvisor(undefined), home: dir })),
    /nothing to write/,
  );
});
