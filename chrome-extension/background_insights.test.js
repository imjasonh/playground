import assert from "node:assert/strict";
import test from "node:test";

import { ALARM, startInsights } from "./background_insights.js";

function listener() {
  const handlers = [];
  return {
    addListener(fn) {
      handlers.push(fn);
    },
    async emit(...args) {
      await Promise.all(handlers.map((fn) => fn(...args)));
    },
  };
}

function fakeChrome(tabs, stored = {}) {
  const state = {
    tabs: tabs.map((tab) => ({ groupId: -1, windowId: 1, ...tab })),
    groups: [],
    store: { ...stored },
    alarms: new Map(),
    ungrouped: [],
    nextGroup: 100,
  };
  const api = {
    runtime: { getURL: (path) => `chrome-extension://me/${path}` },
    tabs: {
      async query() {
        return state.tabs.map((tab, index) => ({ index, ...tab }));
      },
      async get(id) {
        return state.tabs.find((tab) => tab.id === id);
      },
      async group({ tabIds, groupId, createProperties }) {
        let id = groupId;
        if (typeof id !== "number") {
          id = state.nextGroup;
          state.nextGroup += 1;
          state.groups.push({ id, windowId: createProperties.windowId, title: "" });
        }
        for (const tab of state.tabs) {
          if (tabIds.includes(tab.id)) {
            tab.groupId = id;
          }
        }
        return id;
      },
      async ungroup(id) {
        state.ungrouped.push(id);
        state.tabs.find((tab) => tab.id === id).groupId = -1;
      },
      onActivated: listener(),
    },
    tabGroups: {
      async query() {
        return state.groups.map((group) => ({ ...group }));
      },
      async get(id) {
        return state.groups.find((group) => group.id === id);
      },
      async update(id, props) {
        Object.assign(state.groups.find((group) => group.id === id), props);
      },
    },
    storage: {
      local: {
        async get(keys) {
          if (typeof keys === "string") {
            return keys in state.store ? { [keys]: structuredClone(state.store[keys]) } : {};
          }
          const out = {};
          for (const [key, fallback] of Object.entries(keys)) {
            out[key] = key in state.store ? state.store[key] : fallback;
          }
          return out;
        },
        async set(values) {
          Object.assign(state.store, structuredClone(values));
        },
      },
      onChanged: listener(),
    },
    alarms: {
      async get(name) {
        return state.alarms.get(name);
      },
      async create(name, info) {
        state.alarms.set(name, { name, ...info });
      },
      onAlarm: listener(),
    },
  };
  return { api, state };
}

function fakeModel(answer, availability = "available") {
  const model = {
    prompts: [],
    destroyed: 0,
    async availability() {
      return availability;
    },
    async create() {
      return {
        async prompt(text) {
          model.prompts.push(text);
          return JSON.stringify(answer);
        },
        destroy() {
          model.destroyed += 1;
        },
      };
    },
  };
  return model;
}

const tabs = [
  { id: 1, title: "Docs", url: "https://docs.example/", active: true },
  { id: 2, title: "More docs", url: "https://docs.example/more" },
  { id: 3, title: "New Tab", url: "chrome://newtab/" },
];
const answer = {
  topics: [{ name: "Docs", tabs: [1, 2] }],
  close: [{ tab: 3, reason: "Empty new tab" }],
};

test("startup schedules the background analysis once", async () => {
  const { api, state } = fakeChrome(tabs);
  await startInsights(api, fakeModel(answer)).ready;
  assert.deepEqual(state.alarms.get(ALARM), { name: ALARM, delayInMinutes: 1, periodInMinutes: 15 });
  state.alarms.set(ALARM, { name: ALARM, periodInMinutes: 99 });
  await startInsights(api, fakeModel(answer)).ready;
  assert.equal(state.alarms.get(ALARM).periodInMinutes, 99);
});

test("the alarm saves picks and topics without grouping by default", async () => {
  const { api, state } = fakeChrome(tabs);
  const model = fakeModel(answer);
  startInsights(api, model);
  await api.alarms.onAlarm.emit({ name: ALARM });
  const saved = state.store.insights;
  assert.equal(saved.read, 3);
  assert.deepEqual(saved.insights.close.map((pick) => pick.entry.id), [3]);
  assert.deepEqual(saved.insights.topics.map((topic) => topic.name), ["Docs"]);
  assert.equal(model.destroyed, 1);
  assert.deepEqual(state.groups, []);
  assert.equal("grouping" in state.store, false);
});

test("a second run with the same tabs skips the model", async () => {
  const { api } = fakeChrome(tabs);
  const model = fakeModel(answer);
  const insights = startInsights(api, model);
  await insights.run();
  await insights.run();
  assert.equal(model.prompts.length, 1);
});

test("background off, a model to download, or no Prompt API means no run", async () => {
  for (const [stored, model] of [
    [{ background: false }, fakeModel(answer)],
    [{}, fakeModel(answer, "downloadable")],
    [{}, null],
  ]) {
    const { api, state } = fakeChrome(tabs, stored);
    await startInsights(api, model).run();
    assert.equal("insights" in state.store, false);
  }
});

test("automatic grouping makes the groups and saves positions for undo", async () => {
  const { api, state } = fakeChrome(tabs, { autoGroup: true });
  startInsights(api, fakeModel(answer));
  await api.alarms.onAlarm.emit({ name: ALARM });
  assert.deepEqual(
    state.groups.map((group) => [group.title, group.color, group.collapsed]),
    [
      ["Likely close", "grey", true],
      ["Docs", "blue", false],
    ],
  );
  assert.deepEqual(state.store.grouping.saved.map((tab) => tab.id), [3, 1, 2]);
  assert.equal(state.store.grouping.at, state.store.insights.at);
});

test("the model sees existing group names, and a run adds to the matching group", async () => {
  const { api, state } = fakeChrome(
    [...tabs, { id: 4, title: "Old docs", url: "https://docs.example/old", groupId: 50 }],
    { autoGroup: true },
  );
  state.groups.push({ id: 50, windowId: 1, title: "Docs", color: "green" });
  const model = fakeModel(answer);
  startInsights(api, model);
  await api.alarms.onAlarm.emit({ name: ALARM });
  assert.match(model.prompts[0], /\(group: Docs\) Old docs/);
  assert.deepEqual(state.tabs.filter((tab) => tab.groupId === 50).map((tab) => tab.id), [1, 2, 4]);
  assert.equal(state.groups.find((group) => group.id === 50).color, "green");
});

test("switching to a pick removes it from the picks and the Likely close group", async () => {
  const { api, state } = fakeChrome(tabs, { autoGroup: true });
  startInsights(api, fakeModel(answer));
  await api.alarms.onAlarm.emit({ name: ALARM });
  await api.tabs.onActivated.emit({ tabId: 3, windowId: 1 });
  assert.deepEqual(state.store.insights.insights.close, []);
  assert.deepEqual(state.ungrouped, [3]);
  await api.tabs.onActivated.emit({ tabId: 2, windowId: 1 });
  assert.deepEqual(state.ungrouped, [3]);
});

test("turning background analysis on runs it", async () => {
  const { api, state } = fakeChrome(tabs);
  startInsights(api, fakeModel(answer));
  await api.storage.onChanged.emit({ background: { newValue: true } }, "local");
  assert.equal(state.store.insights.read, 3);
});
