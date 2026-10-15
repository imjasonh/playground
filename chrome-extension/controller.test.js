import assert from "node:assert/strict";
import test from "node:test";

import { actionTitle, badgeText } from "./duplicates.js";
import { start } from "./controller.js";

function deferred() {
  let resolve = () => {};
  const promise = new Promise((done) => {
    resolve = done;
  });
  return { promise, resolve };
}

function listener() {
  const handlers = [];
  return {
    addListener(fn) {
      handlers.push(fn);
    },
    async emit(...args) {
      const pending = handlers.map((fn) => fn(...args));
      await Promise.all(pending);
    },
  };
}

function fakeChrome(initial) {
  const state = {
    tabs: initial.map((tab) => ({ ...tab })),
    badge: null,
    color: null,
    textColor: null,
    title: null,
    removed: [],
    queries: 0,
    holdQuery: deferred(),
  };
  const api = {
    tabs: {
      async query() {
        state.queries += 1;
        await state.holdQuery.promise;
        return state.tabs.map((tab) => ({ ...tab }));
      },
      async remove(ids) {
        state.removed.push(ids);
        const drop = new Set(ids);
        state.tabs = state.tabs.filter((tab) => !drop.has(tab.id));
      },
      onCreated: listener(),
      onRemoved: listener(),
      onUpdated: listener(),
      onReplaced: listener(),
      onAttached: listener(),
      onDetached: listener(),
    },
    action: {
      async setBadgeText({ text }) {
        state.badge = text;
      },
      async setBadgeBackgroundColor({ color }) {
        state.color = color;
      },
      async setBadgeTextColor({ color }) {
        state.textColor = color;
      },
      async setTitle({ title }) {
        state.title = title;
      },
      onClicked: listener(),
    },
    contextMenus: {
      async update(id, props) {
        if (!state.menu || state.menu.id !== id) {
          throw new Error(`Cannot find menu item with id ${id}`);
        }
        state.menu = { ...state.menu, ...props };
      },
      async create(props) {
        if (state.menu && state.menu.id === props.id) {
          throw new Error(`Cannot create item with duplicate id ${props.id}`);
        }
        state.menu = { ...props };
      },
      onClicked: listener(),
    },
    runtime: {
      onInstalled: listener(),
      onStartup: listener(),
    },
  };
  return { api, state };
}

test("startup sets the badge to the number of tabs a click will close", async () => {
  const { api, state } = fakeChrome([
    { id: 1, url: "https://example.com/a", active: true },
    { id: 2, url: "https://example.com/a" },
    { id: 3, url: "https://example.com/b" },
  ]);
  const ready = start(api);
  state.holdQuery.resolve();
  await ready;
  assert.equal(state.badge, "1");
  assert.equal(state.title, "Close 1 duplicate tab");
  assert.equal(state.color, "#174ea6");
  assert.equal(state.textColor, "#ffffff");
  assert.equal(state.menu.title, "Close 1 duplicate tab");
  assert.equal(state.menu.visible, true);
  assert.deepEqual(state.menu.contexts, ["tab"]);
});

test("the toolbar click closes the duplicate tabs and clears the badge", async () => {
  const { api, state } = fakeChrome([
    { id: 1, url: "https://example.com/a", pinned: true },
    { id: 2, url: "https://example.com/a", active: true },
    { id: 3, url: "https://example.com/a" },
    { id: 4, url: "https://example.com/b" },
    { id: 5, url: "https://example.com/b" },
  ]);
  const ready = start(api);
  state.holdQuery.resolve();
  await ready;
  assert.equal(state.badge, "3");
  await api.action.onClicked.emit();
  assert.deepEqual(state.removed, [[2, 3, 5]]);
  assert.deepEqual(state.tabs.map((tab) => tab.id), [1, 4]);
  assert.equal(state.badge, "");
  assert.equal(state.title, "No duplicate tabs");
  assert.equal(state.menu.visible, false);
});

test("the tab menu item closes the same tabs as the toolbar button", async () => {
  const { api, state } = fakeChrome([
    { id: 1, url: "https://example.com/a", active: true },
    { id: 2, url: "https://example.com/a" },
    { id: 3, url: "https://example.com/b" },
  ]);
  const ready = start(api);
  state.holdQuery.resolve();
  await ready;
  await api.contextMenus.onClicked.emit({ menuItemId: "close-duplicates" }, { id: 2 });
  assert.deepEqual(state.removed, [[2]]);
  assert.equal(state.menu.visible, false);
  assert.equal(state.badge, "");
});

test("a tab menu click for another item does not close tabs", async () => {
  const { api, state } = fakeChrome([
    { id: 1, url: "https://example.com/a", active: true },
    { id: 2, url: "https://example.com/a" },
  ]);
  const ready = start(api);
  state.holdQuery.resolve();
  await ready;
  await api.contextMenus.onClicked.emit({ menuItemId: "other" });
  assert.deepEqual(state.removed, []);
  assert.equal(state.menu.visible, true);
});

test("a URL change refreshes the badge", async () => {
  const { api, state } = fakeChrome([
    { id: 1, url: "https://example.com/a", active: true },
    { id: 2, url: "https://example.com/b" },
  ]);
  const ready = start(api);
  state.holdQuery.resolve();
  await ready;
  assert.equal(state.badge, badgeText(0));
  assert.equal(state.title, actionTitle(0));
  assert.equal(state.menu.visible, false);
  state.tabs[1].url = "https://example.com/a";
  const before = state.queries;
  await api.tabs.onUpdated.emit(2, { url: "https://example.com/a" });
  assert.ok(state.queries > before);
  assert.equal(state.badge, "1");
  assert.equal(state.title, "Close 1 duplicate tab");
  assert.equal(state.menu.title, "Close 1 duplicate tab");
  assert.equal(state.menu.visible, true);
});

test("an unsupported tab menu still sets the badge", async () => {
  const { api, state } = fakeChrome([
    { id: 1, url: "https://example.com/a", active: true },
    { id: 2, url: "https://example.com/a" },
  ]);
  api.contextMenus.update = async () => {
    throw new Error("Cannot find menu item with id close-duplicates");
  };
  api.contextMenus.create = async () => {
    throw new Error("Invalid value for argument contexts");
  };
  const errors = [];
  const original = console.error;
  console.error = (...args) => {
    errors.push(args);
  };
  try {
    const ready = start(api);
    state.holdQuery.resolve();
    await ready;
  } finally {
    console.error = original;
  }
  assert.equal(state.badge, "1");
  assert.equal(errors.length, 1);
  const before = state.queries;
  await api.tabs.onCreated.emit();
  assert.ok(state.queries > before);
  assert.equal(errors.length, 1);
});

test("favicon updates do not query tabs again", async () => {
  const { api, state } = fakeChrome([{ id: 1, url: "https://example.com/a" }]);
  const ready = start(api);
  state.holdQuery.resolve();
  await ready;
  const before = state.queries;
  await api.tabs.onUpdated.emit(1, { favIconUrl: "https://example.com/favicon.ico" });
  assert.equal(state.queries, before);
});
