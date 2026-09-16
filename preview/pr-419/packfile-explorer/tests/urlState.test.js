import test from "node:test";
import assert from "node:assert/strict";

import { packShareUrl, readUrlState, writeUrlState } from "../src/urlState.js";

const OID = "a".repeat(40);

test("readUrlState reads pack query and object hash", () => {
  const loc = {
    href: "https://example.github.io/playground/packfile-explorer/?pack=https%3A%2F%2Fgithub.com%2Fa%2Fb.git#" + OID,
    pathname: "/playground/packfile-explorer/",
    search: "?pack=https%3A%2F%2Fgithub.com%2Fa%2Fb.git",
    hash: `#${OID}`,
  };
  const state = readUrlState(loc);
  assert.equal(state.packId, "https://github.com/a/b.git");
  assert.equal(state.objectId, OID);
});

test("readUrlState ignores invalid object hashes", () => {
  const loc = {
    href: "https://example.github.io/app/?pack=file%3A%2F%2Fx.pack#not-an-oid",
    pathname: "/app/",
    search: "?pack=file%3A%2F%2Fx.pack",
    hash: "#not-an-oid",
  };
  assert.deepEqual(readUrlState(loc), { packId: "file://x.pack", objectId: null });
});

test("packShareUrl encodes pack id and oid", () => {
  const loc = {
    href: "https://example.github.io/playground/packfile-explorer/",
    pathname: "/playground/packfile-explorer/",
    search: "",
    hash: "",
  };
  const url = packShareUrl("https://github.com/a/b.git", OID, loc);
  assert.equal(
    url,
    `https://example.github.io/playground/packfile-explorer/?pack=${encodeURIComponent("https://github.com/a/b.git")}#${OID}`,
  );
});

test("writeUrlState sets search and hash via replaceState", () => {
  const calls = [];
  const loc = {
    href: "https://example.github.io/app/",
    pathname: "/app/",
    search: "",
    hash: "",
  };
  const fakeHistory = { replaceState: (...args) => calls.push(args) };
  writeUrlState({ packId: "file://demo.pack", objectId: OID }, loc, fakeHistory);
  assert.equal(calls.length, 1);
  assert.equal(calls[0][2], `/app/?pack=${encodeURIComponent("file://demo.pack")}#${OID}`);
});
