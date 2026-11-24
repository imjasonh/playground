import test from "node:test";
import assert from "node:assert/strict";

import {
  createNavHistory,
  normalizeNavTarget,
  packShareUrl,
  readUrlState,
  sameNavTarget,
  writeUrlState,
} from "../src/urlState.js";

const OID = "a".repeat(40);
const OID_B = "b".repeat(40);
const OID_C = "c".repeat(40);

function makeFakeBrowser(initialHref = "https://example.github.io/app/") {
  const stack = [{ url: new URL(initialHref), state: null }];
  let cursor = 0;

  const locationLike = {
    get href() {
      return stack[cursor].url.href;
    },
    get pathname() {
      return stack[cursor].url.pathname;
    },
    get search() {
      return stack[cursor].url.search;
    },
    get hash() {
      return stack[cursor].url.hash;
    },
  };

  let popListener = null;

  const historyLike = {
    get state() {
      return stack[cursor].state;
    },
    pushState(state, _title, url) {
      stack.splice(cursor + 1);
      stack.push({ url: new URL(url, stack[cursor].url), state });
      cursor = stack.length - 1;
    },
    replaceState(state, _title, url) {
      stack[cursor] = { url: new URL(url, stack[cursor].url), state };
    },
    back() {
      if (cursor === 0) throw new Error("left the app!");
      cursor -= 1;
      popListener?.(stack[cursor].state);
    },
    forward() {
      if (cursor >= stack.length - 1) return;
      cursor += 1;
      popListener?.(stack[cursor].state);
    },
  };

  return {
    locationLike,
    historyLike,
    stack,
    get cursor() {
      return cursor;
    },
    setPopListener(fn) {
      popListener = fn;
    },
    navigateExternalHash(hash) {
      const next = new URL(stack[cursor].url.href);
      next.hash = hash;
      stack.splice(cursor + 1);
      stack.push({ url: next, state: null });
      cursor = stack.length - 1;
      popListener?.(null);
    },
  };
}

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

test("writeUrlState pushes search and hash by default, and supports replace", () => {
  const pushes = [];
  const replaces = [];
  const loc = {
    href: "https://example.github.io/app/",
    pathname: "/app/",
    search: "",
    hash: "",
  };
  const fakeHistory = {
    pushState: (...args) => pushes.push(args),
    replaceState: (...args) => replaces.push(args),
  };
  writeUrlState({ packId: "file://demo.pack", objectId: OID }, loc, fakeHistory);
  assert.equal(pushes.length, 1);
  assert.equal(replaces.length, 0);
  assert.equal(pushes[0][2], `/app/?pack=${encodeURIComponent("file://demo.pack")}#${OID}`);

  writeUrlState({ packId: "file://demo.pack", objectId: null }, loc, fakeHistory, { replace: true });
  assert.equal(replaces.length, 1);
  assert.equal(replaces[0][2], `/app/?pack=${encodeURIComponent("file://demo.pack")}`);
});

test("normalizeNavTarget and sameNavTarget handle landing, overview, object, and unresolved entries", () => {
  const landing = normalizeNavTarget({});
  assert.deepEqual(landing, { packId: null, view: "landing", objectId: null, objectIndex: null });

  const overview = normalizeNavTarget({ packId: "file://a.pack" });
  assert.deepEqual(overview, { packId: "file://a.pack", view: "overview", objectId: null, objectIndex: null });

  const obj = normalizeNavTarget({ packId: "file://a.pack", objectId: OID });
  assert.deepEqual(obj, { packId: "file://a.pack", view: "object", objectId: OID, objectIndex: null });

  const unresolved = normalizeNavTarget({ packId: "file://a.pack", view: "object", objectIndex: 7 });
  assert.deepEqual(unresolved, { packId: "file://a.pack", view: "object", objectId: null, objectIndex: 7 });

  assert.equal(sameNavTarget(overview, unresolved), false);
  assert.equal(sameNavTarget(unresolved, { ...unresolved }), true);
});

test("createNavHistory pushes history entries and traverses back/forward without leaving the app", () => {
  const browser = makeFakeBrowser("https://example.github.io/app/");
  const nav = createNavHistory({
    locationLike: browser.locationLike,
    historyLike: browser.historyLike,
    sessionId: "s1",
  });
  const popped = [];
  browser.setPopListener((state) => popped.push(nav.onPopState(state)));

  // Boot at landing.
  assert.deepEqual(nav.init(), { packId: null, view: "landing", objectId: null, objectIndex: null });
  assert.equal(nav.canBack(), false);
  assert.equal(nav.canForward(), false);
  assert.equal(browser.stack.length, 1);

  // Open pack -> overview.
  assert.equal(nav.push({ packId: "file://demo.pack", view: "overview" }), true);
  assert.equal(browser.stack.length, 2);
  assert.equal(nav.canBack(), true);
  assert.equal(nav.canForward(), false);

  // Duplicate push is ignored.
  assert.equal(nav.push({ packId: "file://demo.pack", view: "overview" }), false);
  assert.equal(browser.stack.length, 2);

  // Navigate to OID -> OID_B -> back to overview.
  assert.equal(nav.push({ packId: "file://demo.pack", view: "object", objectId: OID }), true);
  assert.equal(nav.push({ packId: "file://demo.pack", view: "object", objectId: OID_B }), true);
  assert.equal(nav.push({ packId: "file://demo.pack", view: "overview" }), true);
  assert.equal(browser.stack.length, 5);

  // Back through overview -> OID_B -> OID -> overview -> landing.
  assert.equal(nav.back(), true);
  assert.deepEqual(popped.at(-1), { packId: "file://demo.pack", view: "object", objectId: OID_B, objectIndex: null });
  assert.equal(nav.canForward(), true);

  assert.equal(nav.back(), true);
  assert.deepEqual(popped.at(-1), { packId: "file://demo.pack", view: "object", objectId: OID, objectIndex: null });

  assert.equal(nav.back(), true);
  assert.deepEqual(popped.at(-1), { packId: "file://demo.pack", view: "overview", objectId: null, objectIndex: null });

  assert.equal(nav.back(), true);
  assert.deepEqual(popped.at(-1), { packId: null, view: "landing", objectId: null, objectIndex: null });
  assert.equal(nav.canBack(), false);

  // At landing (pos === 0), toolbar back refuses to leave the app.
  assert.equal(nav.back(), false);
  assert.equal(browser.cursor, 0);

  // Forward restores overview and OID.
  assert.equal(nav.forward(), true);
  assert.deepEqual(popped.at(-1), { packId: "file://demo.pack", view: "overview", objectId: null, objectIndex: null });
  assert.equal(nav.forward(), true);
  assert.deepEqual(popped.at(-1), { packId: "file://demo.pack", view: "object", objectId: OID, objectIndex: null });

  // Pushing a new object truncates the forward stack.
  assert.equal(nav.push({ packId: "file://demo.pack", view: "object", objectId: OID_C }), true);
  assert.equal(nav.canForward(), false);
  assert.equal(browser.stack.length, 4);
});

test("createNavHistory preserves unresolved objectIndex and survives reload/external hash", () => {
  const browser = makeFakeBrowser(`https://example.github.io/app/?pack=${encodeURIComponent("file://thin.pack")}#${OID}`);
  const nav = createNavHistory({
    locationLike: browser.locationLike,
    historyLike: browser.historyLike,
    sessionId: "s2",
  });
  const popped = [];
  browser.setPopListener((state) => popped.push(nav.onPopState(state)));

  // Opening a deep link starts at pos 0 with toolbar Back disabled.
  assert.deepEqual(nav.init(), { packId: "file://thin.pack", view: "object", objectId: OID, objectIndex: null });
  assert.equal(nav.canBack(), false);

  // Navigate to an unresolved object (no oid, has objectIndex).
  assert.equal(nav.push({ packId: "file://thin.pack", view: "object", objectIndex: 42 }), true);
  assert.equal(nav.canBack(), true);

  // Simulate page reload at pos 1: a fresh controller picks up session/pos/objectIndex from history.state.
  const reloaded = createNavHistory({
    locationLike: browser.locationLike,
    historyLike: browser.historyLike,
    sessionId: "s3",
  });
  assert.deepEqual(reloaded.init(), { packId: "file://thin.pack", view: "object", objectId: null, objectIndex: 42 });
  assert.equal(reloaded.canBack(), true);

  // Going back returns to OID.
  browser.setPopListener((state) => popped.push(reloaded.onPopState(state)));
  assert.equal(reloaded.back(), true);
  assert.deepEqual(popped.at(-1), { packId: "file://thin.pack", view: "object", objectId: OID, objectIndex: null });
  assert.equal(reloaded.canBack(), false);

  // Manual hash edit (state === null) derives target from URL.
  browser.navigateExternalHash(`#${OID_B}`);
  assert.deepEqual(popped.at(-1), { packId: "file://thin.pack", view: "object", objectId: OID_B, objectIndex: null });
});
