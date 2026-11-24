import assert from "node:assert/strict";
import test from "node:test";

import { ALARM, SOON_ALARM, startInsights } from "./background_insights.js";

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

function fakeChrome(tabs) {
  const state = {
    tabs: tabs.map((tab) => ({ groupId: -1, windowId: 1, ...tab })),
    groups: [],
    store: {},
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
      onCreated: listener(),
      onRemoved: listener(),
      onUpdated: listener(),
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
        async get(key) {
          return key in state.store ? { [key]: structuredClone(state.store[key]) } : {};
        },
        async set(values) {
          Object.assign(state.store, structuredClone(values));
        },
      },
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

test("the alarm saves the plan and never groups tabs", async () => {
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
  assert.ok(state.tabs.every((tab) => tab.groupId === -1));
});

test("tab changes schedule a run a minute after the last one", async () => {
  const { api, state } = fakeChrome(tabs);
  startInsights(api, fakeModel(answer));
  await api.tabs.onUpdated.emit(1, { favIconUrl: "x" });
  assert.equal(state.alarms.has(SOON_ALARM), false);
  await api.tabs.onCreated.emit({ id: 9 });
  await api.tabs.onRemoved.emit(9);
  await api.tabs.onUpdated.emit(1, { url: "https://docs.example/new" });
  assert.deepEqual(state.alarms.get(SOON_ALARM), { name: SOON_ALARM, delayInMinutes: 1 });
  await api.alarms.onAlarm.emit({ name: SOON_ALARM });
  assert.equal(state.store.insights.read, 3);
});

test("a second run with the same tabs skips the model", async () => {
  const { api } = fakeChrome(tabs);
  const model = fakeModel(answer);
  const insights = startInsights(api, model);
  await insights.run();
  await insights.run();
  assert.equal(model.prompts.length, 1);
});

test("a model to download or no Prompt API means no run", async () => {
  for (const model of [fakeModel(answer, "downloadable"), null]) {
    const { api, state } = fakeChrome(tabs);
    await startInsights(api, model).run();
    assert.equal("insights" in state.store, false);
  }
});

test("the model sees existing group names", async () => {
  const { api, state } = fakeChrome([
    ...tabs,
    { id: 4, title: "Old docs", url: "https://docs.example/old", groupId: 50 },
  ]);
  state.groups.push({ id: 50, windowId: 1, title: "Docs", color: "green" });
  const model = fakeModel(answer);
  await startInsights(api, model).run();
  assert.match(model.prompts[0], /\(group: Docs\) Old docs/);
});

test("switching to a pick removes it from the picks and the Likely close group", async () => {
  const { api, state } = fakeChrome(tabs);
  await startInsights(api, fakeModel(answer)).run();
  state.groups.push({ id: 60, windowId: 1, title: "Likely close" });
  state.tabs.find((tab) => tab.id === 3).groupId = 60;
  await api.tabs.onActivated.emit({ tabId: 3, windowId: 1 });
  assert.deepEqual(state.store.insights.insights.close, []);
  assert.deepEqual(state.ungrouped, [3]);
  await api.tabs.onActivated.emit({ tabId: 2, windowId: 1 });
  assert.deepEqual(state.ungrouped, [3]);
});

test("a topic over the limit is split by a second prompt on a clean clone", async () => {
  const pulls = [];
  for (let id = 1; id <= 12; id += 1) {
    pulls.push({ id, title: `PR ${id}`, url: `https://github.com/org/${id <= 6 ? "web" : "api"}/pull/${id}` });
  }
  const { api, state } = fakeChrome(pulls);
  const answers = [
    { topics: [{ name: "Development", tabs: pulls.map((tab) => tab.id) }], close: [] },
    { groups: [{ name: "Web", tabs: [1, 2, 3, 4, 5, 6] }, { name: "API", tabs: [7, 8, 9, 10, 11, 12] }] },
  ];
  const model = { prompts: [], live: 0 };
  function session(history) {
    model.live += 1;
    return {
      async prompt(text) {
        history.push(text);
        model.prompts.push({ text, history: [...history] });
        return JSON.stringify(answers.shift());
      },
      async clone() {
        return session([...history]);
      },
      destroy() {
        model.live -= 1;
      },
    };
  }
  model.availability = async () => "available";
  model.create = async () => session([]);
  await startInsights(api, model).run();
  assert.deepEqual(
    state.store.insights.insights.topics.map((topic) => [topic.name, topic.tabs.length]),
    [
      ["Web", 6],
      ["API", 6],
    ],
  );
  assert.equal(model.prompts.length, 2);
  assert.match(model.prompts[1].text, /grouped as "Development"/);
  assert.equal(model.prompts[1].history.length, 1);
  assert.equal(model.live, 0);
});
