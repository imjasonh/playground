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
    menus: new Map(),
    copied: [],
    messages: [],
    offscreenOpen: false,
    offscreenOptions: null,
    panels: [],
  };
  Object.defineProperty(state, "menu", {
    get() {
      return state.menus.get("close-duplicates");
    },
  });
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
        const menu = state.menus.get(id);
        if (!menu) {
          throw new Error(`Cannot find menu item with id ${id}`);
        }
        state.menus.set(id, { ...menu, ...props });
      },
      async create(props) {
        if (state.menus.has(props.id)) {
          throw new Error(`Cannot create item with duplicate id ${props.id}`);
        }
        state.menus.set(props.id, { ...props });
      },
      onClicked: listener(),
    },
    sidePanel: {
      async open(options) {
        state.panels.push(options);
      },
    },
    offscreen: {
      async hasDocument() {
        return state.offscreenOpen;
      },
      async createDocument(options) {
        state.offscreenOptions = options;
        state.offscreenOpen = true;
      },
    },
    runtime: {
      onInstalled: listener(),
      onStartup: listener(),
      onMessage: listener(),
      async sendMessage(message) {
        state.messages.push(message);
        state.offscreenOpen = false;
      },
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
  assert.deepEqual(state.messages, []);
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
    assert.equal(state.badge, "1");
    assert.equal(errors.length, 3);
    const before = state.queries;
    await api.tabs.onCreated.emit();
    assert.ok(state.queries > before);
    assert.equal(errors.length, 3);
  } finally {
    console.error = original;
  }
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

function decodeMenu(state) {
  return state.menus.get("decode-base64");
}

async function started(tabs) {
  const chrome = fakeChrome(tabs);
  const ready = start(chrome.api);
  chrome.state.holdQuery.resolve();
  await ready;
  return chrome;
}

test("startup leaves the selection menu hidden", async () => {
  const { state } = await started([{ id: 1, url: "https://example.com/a" }]);
  const decode = decodeMenu(state);
  assert.equal(decode.visible, false);
  assert.equal(decode.title, "Decoded");
  assert.deepEqual(decode.contexts, ["selection"]);
  assert.equal(state.menu.contexts[0], "tab");
});

test("a base64 selection shows the decoded text and does not close tabs", async () => {
  const { api, state } = await started([
    { id: 1, url: "https://example.com/a", active: true },
    { id: 2, url: "https://example.com/a" },
  ]);
  const badge = state.badge;
  await api.runtime.onMessage.emit(
    { type: "selection", text: "\n  aGVsbG8=\t" },
    { tab: { id: 2 }, frameId: 0 },
  );
  const decode = decodeMenu(state);
  assert.equal(decode.visible, true);
  assert.equal(decode.title, "hello");
  assert.deepEqual(decode.contexts, ["selection"]);
  assert.equal(state.badge, badge);
  assert.deepEqual(state.removed, []);
  await api.contextMenus.onClicked.emit({
    menuItemId: "decode-base64",
    selectionText: "not-the-selection",
  });
  assert.deepEqual(state.removed, []);
  assert.deepEqual(state.messages, [
    {
      target: "offscreen-clipboard",
      type: "copy",
      text: "hello",
    },
  ]);
  assert.equal(state.offscreenOptions.url, "offscreen.html");
  assert.deepEqual(state.offscreenOptions.reasons, ["CLIPBOARD"]);
  assert.equal(
    state.offscreenOptions.justification,
    "Copy decoded base64 text to the clipboard.",
  );
});

test("text that is not base64 adds no selection item", async () => {
  const { api, state } = await started([{ id: 1, url: "https://example.com/a" }]);
  await api.runtime.onMessage.emit(
    { type: "selection", text: "  aGVs bG8=  " },
    { tab: { id: 1 }, frameId: 0 },
  );
  assert.equal(decodeMenu(state).visible, false);
  await api.runtime.onMessage.emit(
    { type: "selection", text: "hello" },
    { tab: { id: 1 }, frameId: 0 },
  );
  assert.equal(decodeMenu(state).visible, false);
  await api.contextMenus.onClicked.emit({
    menuItemId: "decode-base64",
    selectionText: "hello",
  });
  assert.deepEqual(state.messages, []);
});

test("clearing the selection removes the decode item, and another frame does not", async () => {
  const { api, state } = await started([{ id: 1, url: "https://example.com/a" }]);
  await api.runtime.onMessage.emit(
    { type: "selection", text: "aGVsbG8=" },
    { tab: { id: 1 }, frameId: 0 },
  );
  assert.equal(decodeMenu(state).title, "hello");
  await api.runtime.onMessage.emit(
    { type: "selection", text: "hello" },
    { tab: { id: 1 }, frameId: 1 },
  );
  assert.equal(decodeMenu(state).visible, true);
  assert.equal(decodeMenu(state).title, "hello");
  await api.runtime.onMessage.emit(
    { type: "selection", text: "" },
    { tab: { id: 1 }, frameId: 0 },
  );
  assert.equal(decodeMenu(state).visible, false);
  await api.contextMenus.onClicked.emit({
    menuItemId: "decode-base64",
    selectionText: "",
  });
  assert.deepEqual(state.messages, []);
});

test("a non-base64 selection hides a decode item restored after restart", async () => {
  const chrome = fakeChrome([{ id: 1, url: "https://example.com/a" }]);
  chrome.state.menus.set("decode-base64", {
    id: "decode-base64",
    title: "hello",
    contexts: ["selection"],
    visible: true,
  });
  const ready = start(chrome.api);
  chrome.state.holdQuery.resolve();
  await ready;
  assert.equal(decodeMenu(chrome.state).visible, true);
  assert.equal(decodeMenu(chrome.state).title, "hello");
  await chrome.api.runtime.onMessage.emit(
    { type: "selection", text: "hello world" },
    { tab: { id: 1 }, frameId: 0 },
  );
  assert.equal(decodeMenu(chrome.state).visible, false);
  await chrome.api.contextMenus.onClicked.emit({
    menuItemId: "decode-base64",
    selectionText: "hello world",
  });
  assert.deepEqual(chrome.state.messages, []);
});

test("the toolbar button's menu opens tab insights in that window's side panel", async () => {
  const { api, state } = await started([
    { id: 1, url: "https://example.com/a", active: true },
    { id: 2, url: "https://example.com/a" },
  ]);
  const item = state.menus.get("tab-insights");
  assert.equal(item.title, "Tab insights");
  assert.deepEqual(item.contexts, ["action"]);
  await api.contextMenus.onClicked.emit({ menuItemId: "tab-insights" }, { id: 1, windowId: 4 });
  assert.deepEqual(state.panels, [{ windowId: 4 }]);
  assert.deepEqual(state.removed, []);
  assert.equal(state.badge, "1");
});

test("tab insights survives a restart that kept its menu item", async () => {
  const chrome = fakeChrome([{ id: 1, url: "https://example.com/a" }]);
  chrome.state.menus.set("tab-insights", { id: "tab-insights", title: "Tab insights", contexts: ["action"] });
  const errors = [];
  const original = console.error;
  console.error = (...args) => {
    errors.push(args);
  };
  try {
    const ready = start(chrome.api);
    chrome.state.holdQuery.resolve();
    await ready;
  } finally {
    console.error = original;
  }
  assert.deepEqual(errors, []);
  assert.equal(chrome.state.menus.get("tab-insights").title, "Tab insights");
});

test("Chrome without the side panel API gets no tab insights item", async () => {
  const chrome = fakeChrome([{ id: 1, url: "https://example.com/a" }]);
  delete chrome.api.sidePanel;
  const ready = start(chrome.api);
  chrome.state.holdQuery.resolve();
  await ready;
  assert.equal(chrome.state.menus.has("tab-insights"), false);
  await chrome.api.contextMenus.onClicked.emit({ menuItemId: "tab-insights" }, { id: 1, windowId: 4 });
  assert.deepEqual(chrome.state.panels, []);
});

function withStorage(chrome, store) {
  const changed = listener();
  chrome.api.storage = {
    local: {
      async get(keys) {
        const out = {};
        for (const key of keys) {
          if (key in store) {
            out[key] = store[key];
          }
        }
        return out;
      },
    },
    onChanged: changed,
  };
  return changed;
}

test("an unseen plan turns the badge green and adds to the title until the panel shows it", async () => {
  const chrome = fakeChrome([
    { id: 1, url: "https://example.com/a", active: true },
    { id: 2, url: "https://example.com/a" },
    { id: 3, url: "https://example.com/b" },
  ]);
  const store = {
    insights: {
      at: 5,
      insights: { close: [{ entry: { id: 3 } }, { entry: { id: 9 } }], topics: [] },
    },
  };
  const changed = withStorage(chrome, store);
  const ready = start(chrome.api);
  chrome.state.holdQuery.resolve();
  await ready;
  assert.equal(chrome.state.title, "Close 1 duplicate tab · grouping ready · 1 likely close");
  assert.equal(chrome.state.badge, "1");
  assert.equal(chrome.state.color, "#188038");
  assert.equal(chrome.state.menu.title, "Close 1 duplicate tab");
  store.seen = 5;
  await changed.emit({ seen: { newValue: 5 } }, "local");
  assert.equal(chrome.state.title, "Close 1 duplicate tab · 1 likely close");
  assert.equal(chrome.state.color, "#174ea6");
  store.insights.insights.close = [];
  await changed.emit({ insights: { newValue: store.insights } }, "local");
  assert.equal(chrome.state.title, "Close 1 duplicate tab");
});

test("with no duplicates, a ready plan shows a dot, and a plan with nothing to group shows none", async () => {
  const chrome = fakeChrome([
    { id: 1, url: "https://example.com/a", active: true },
    { id: 2, url: "https://example.com/b", groupId: 40 },
  ]);
  const store = {
    insights: { at: 7, insights: { close: [], topics: [{ name: "A", tabs: [{ id: 1 }, { id: 2 }] }] } },
  };
  const changed = withStorage(chrome, store);
  const ready = start(chrome.api);
  chrome.state.holdQuery.resolve();
  await ready;
  assert.equal(chrome.state.badge, "•");
  assert.equal(chrome.state.color, "#188038");
  assert.equal(chrome.state.title, "No duplicate tabs · grouping ready");
  chrome.state.tabs[0].groupId = 41;
  await changed.emit({ insights: { newValue: store.insights } }, "local");
  assert.equal(chrome.state.badge, "");
  assert.equal(chrome.state.title, "No duplicate tabs");
});

test("a selection menu click after restart decodes the highlighted text", async () => {
  const { api, state } = await started([{ id: 1, url: "https://example.com/a" }]);
  await api.contextMenus.onClicked.emit({
    menuItemId: "decode-base64",
    selectionText: " YQ== ",
  });
  assert.deepEqual(state.messages, [
    {
      target: "offscreen-clipboard",
      type: "copy",
      text: "a",
    },
  ]);
});
