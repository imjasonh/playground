import assert from "node:assert/strict";
import { test } from "node:test";
import { RC_BEGIN, RC_END } from "../src/prompts.js";
import { backupPath, parseSettingsReply, resolveRcSource } from "../src/settings.js";

const HOME = "/home/player";
const none = () => false;

test("an explicit --file wins over everything", () => {
  const source = resolveRcSource({ fileArg: "/tmp/my.rc", nethackoptions: "autopickup", home: HOME, exists: none });
  assert.deepEqual(source, { kind: "file", path: "/tmp/my.rc" });
});

test("NETHACKOPTIONS with @ names a file, with ~ expanded", () => {
  const source = resolveRcSource({ nethackoptions: "@~/custom.rc", home: HOME, exists: none });
  assert.deepEqual(source, { kind: "file", path: "/home/player/custom.rc" });
});

test("NETHACKOPTIONS that names an existing file is read as a file", () => {
  const source = resolveRcSource({
    nethackoptions: "/etc/nethack.rc",
    home: HOME,
    exists: (p) => p === "/etc/nethack.rc",
  });
  assert.deepEqual(source, { kind: "file", path: "/etc/nethack.rc" });
});

test("a non-file NETHACKOPTIONS value is treated as inline options", () => {
  const source = resolveRcSource({ nethackoptions: "autopickup,pickup_types:$", home: HOME, exists: none });
  assert.deepEqual(source, { kind: "inline", contents: "autopickup,pickup_types:$" });
});

test("nothing set falls back to ~/.nethackrc", () => {
  const source = resolveRcSource({ home: HOME, exists: none });
  assert.deepEqual(source, { kind: "file", path: "/home/player/.nethackrc" });
});

test("a reply with a config block splits into review and config", () => {
  const reply = `Turn off autopickup to avoid clutter.\n${RC_BEGIN}\nOPTIONS=!autopickup\nOPTIONS=color\n${RC_END}\ntrailing chatter`;
  const parsed = parseSettingsReply(reply);
  assert.equal(parsed.review, "Turn off autopickup to avoid clutter.");
  assert.equal(parsed.config, "OPTIONS=!autopickup\nOPTIONS=color");
});

test("a reply with no markers is all review", () => {
  const parsed = parseSettingsReply("Looks fine to me.");
  assert.deepEqual(parsed, { review: "Looks fine to me." });
});

test("the backup path is timestamped so it never clobbers", () => {
  const at = new Date("2026-10-22T20:30:00.000Z");
  assert.equal(backupPath("/home/player/.nethackrc", at), "/home/player/.nethackrc.bak.2026-10-22T20-30-00-000Z");
});
