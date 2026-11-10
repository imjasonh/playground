import assert from "node:assert/strict";
import test from "node:test";

import {
  MAX_CLOSE,
  MAX_TABS,
  closableIds,
  closeLabel,
  formatAge,
  groupingPlan,
  matchRestores,
  parseInsights,
  tabCount,
  tabEntries,
  tabLine,
  undoMoves,
  userPrompt,
  withoutTabs,
} from "./tab_insights.js";

const now = Date.UTC(2026, 10, 10, 12, 0, 0);
const minute = 60000;
const own = "chrome-extension://abc/";

test("the model reads title, host and path, age, and flags, never the query or hash", () => {
  const { entries, total } = tabEntries(
    [
      {
        id: 7,
        windowId: 1,
        title: "Pull request\n  #12",
        url: "https://github.com/o/r/pull/12?token=secret#files",
        lastAccessed: now - 3 * 60 * minute,
        pinned: true,
      },
      { id: 8, windowId: 1, title: "", url: "chrome://history/?q=secret", lastAccessed: now - 2 * 24 * 60 * minute },
      { id: 9, windowId: 2, title: "Song", url: "https://music.example/", active: true, audible: true },
      {
        id: 10,
        windowId: 2,
        title: "https://www.google.com/search?q=secret#files",
        url: "https://www.google.com/sorry/index?continue=secret",
      },
    ],
    now,
    own,
  );
  assert.equal(total, 4);
  assert.deepEqual(entries.map(tabLine), [
    "1. [3h ago] (pinned) Pull request #12 — github.com/o/r/pull/12",
    "2. [2d ago] chrome://history/ — chrome://history/",
    "3. (active, audio) Song — music.example/",
    "4. www.google.com/search — www.google.com/sorry/index",
  ]);
  assert.equal(userPrompt(entries).includes("secret"), false);
  assert.equal(userPrompt(entries).includes("files"), false);
  assert.deepEqual(entries.map((entry) => entry.id), [7, 8, 9, 10]);
});

test("the side panel, tabs without an id, and tabs without a URL are left out", () => {
  const { entries, total } = tabEntries(
    [
      { id: 1, url: `${own}insights.html` },
      { url: "https://example.com/" },
      { id: 2, url: "" },
      { id: 3, url: "about:blank", pendingUrl: "https://example.com/next" },
      { id: 4, url: "", pendingUrl: "https://example.com/loading" },
    ],
    now,
    own,
  );
  assert.equal(total, 2);
  assert.deepEqual(entries.map((entry) => [entry.number, entry.id, entry.location]), [
    [1, 3, "example.com/next"],
    [2, 4, "example.com/loading"],
  ]);
});

test("past the cap, the tabs used longest ago are read, in tab order", () => {
  const tabs = [];
  for (let id = 1; id <= MAX_TABS + 10; id += 1) {
    tabs.push({ id, url: `https://example.com/${id}`, lastAccessed: now - id * minute });
  }
  const { entries, total } = tabEntries(tabs, now, own);
  assert.equal(total, MAX_TABS + 10);
  assert.equal(entries.length, MAX_TABS);
  assert.equal(entries[0].id, 11);
  assert.equal(entries.at(-1).id, MAX_TABS + 10);
  assert.deepEqual(entries.map((entry) => entry.number), [...Array(MAX_TABS).keys()].map((n) => n + 1));
});

test("long titles and paths are clipped", () => {
  const { entries } = tabEntries(
    [{ id: 1, title: "t".repeat(200), url: `https://example.com/${"p".repeat(200)}` }],
    now,
    own,
  );
  assert.equal(entries[0].title.length, 80);
  assert.ok(entries[0].title.endsWith("…"));
  assert.equal(entries[0].location.length, 60);
});

test("ages are minutes, hours, or days", () => {
  assert.equal(formatAge(10 * 1000), "now");
  assert.equal(formatAge(5 * minute), "5m ago");
  assert.equal(formatAge(90 * minute), "1h ago");
  assert.equal(formatAge(49 * 60 * minute), "2d ago");
});

function sample() {
  return tabEntries(
    [
      { id: 10, title: "Docs", url: "https://docs.example/a" },
      { id: 11, title: "Docs again", url: "https://docs.example/b" },
      { id: 12, title: "Pinned mail", url: "https://mail.example/", pinned: true },
      { id: 13, title: "Here now", url: "https://now.example/", active: true },
      { id: 14, title: "Radio", url: "https://radio.example/", audible: true },
      { id: 15, title: "Search", url: "https://search.example/q" },
    ],
    now,
    own,
  ).entries;
}

test("the answer maps tab numbers back to tabs and keeps the reasons", () => {
  const entries = sample();
  const { topics, close } = parseInsights(
    JSON.stringify({
      topics: [
        { name: "Reading docs", tabs: [1, 2] },
        { name: "Other", tabs: [6] },
      ],
      close: [
        { tab: 2, reason: "Same site as tab 1" },
        { tab: 6, reason: "Old search" },
      ],
    }),
    entries,
  );
  assert.deepEqual(
    topics.map((topic) => [topic.name, topic.tabs.map((entry) => entry.id)]),
    [
      ["Reading docs", [10, 11]],
      ["Other", [15]],
    ],
  );
  assert.deepEqual(
    close.map((pick) => [pick.entry.id, pick.reason]),
    [
      [11, "Same site as tab 1"],
      [15, "Old search"],
    ],
  );
});

test("pinned, active, and audible tabs are never suggested", () => {
  const { close } = parseInsights(
    JSON.stringify({
      topics: [],
      close: [
        { tab: 3, reason: "x" },
        { tab: 4, reason: "x" },
        { tab: 5, reason: "x" },
        { tab: 1, reason: "x" },
      ],
    }),
    sample(),
  );
  assert.deepEqual(close.map((pick) => pick.entry.id), [10]);
});

test("unknown numbers, repeats, empty topics, and junk fields are dropped", () => {
  const { topics, close } = parseInsights(
    JSON.stringify({
      topics: [
        { name: "  A  ", tabs: [1, 1, 99, "2"] },
        { name: "B", tabs: [1] },
        { name: "", tabs: [2] },
        { tabs: [2] },
        "junk",
      ],
      close: [{ tab: 99, reason: "x" }, { tab: 1 }, { tab: 1, reason: "again" }, null],
    }),
    sample(),
  );
  assert.deepEqual(
    topics.map((topic) => [topic.name, topic.tabs.map((entry) => entry.number)]),
    [["A", [1]]],
  );
  assert.deepEqual(close.map((pick) => [pick.entry.number, pick.reason]), [[1, ""]]);
});

test("at most MAX_CLOSE tabs are suggested", () => {
  const tabs = [];
  for (let id = 1; id <= MAX_CLOSE + 5; id += 1) {
    tabs.push({ id, url: `https://example.com/${id}` });
  }
  const { entries } = tabEntries(tabs, now, own);
  const { close } = parseInsights(
    JSON.stringify({ topics: [], close: entries.map((entry) => ({ tab: entry.number, reason: "old" })) }),
    entries,
  );
  assert.equal(close.length, MAX_CLOSE);
});

test("an answer that is not JSON is an error, and missing sections are empty", () => {
  assert.throws(() => parseInsights("Sure! Here are", sample()), /not JSON/);
  assert.deepEqual(parseInsights("{}", sample()), { topics: [], close: [] });
});

test("the close button counts the checked tabs", () => {
  assert.equal(closeLabel(0), "Close 0 tabs");
  assert.equal(closeLabel(1), "Close 1 tab");
  assert.equal(closeLabel(3), "Close 3 tabs");
  assert.equal(tabCount(1), "1 tab");
  assert.equal(tabCount(2), "2 tabs");
});

test("a close skips tabs that are gone, pinned, or active now", () => {
  const open = [
    { id: 1 },
    { id: 2, pinned: true },
    { id: 3, active: true },
    { id: 4 },
    { id: 5 },
  ];
  assert.deepEqual(closableIds([1, 2, 3, 4, 9], open), [1, 4]);
});

test("closed tabs leave the suggestions and the topics, and empty topics go", () => {
  const [a, b, c] = sample();
  const insights = {
    close: [{ entry: a, reason: "x" }, { entry: b, reason: "y" }],
    topics: [
      { name: "AB", tabs: [a, b] },
      { name: "C", tabs: [c] },
    ],
  };
  const after = withoutTabs(insights, new Set([a.id, c.id]));
  assert.deepEqual(after.close.map((pick) => pick.entry.id), [b.id]);
  assert.deepEqual(after.topics.map((topic) => [topic.name, topic.tabs.map((entry) => entry.id)]), [["AB", [b.id]]]);
  assert.equal(insights.close.length, 2);
});

test("undo restores each closed tab from the newest matching Recently Closed entry", () => {
  const a = { id: 1, url: "https://a.example/" };
  const b1 = { id: 2, url: "https://b.example/" };
  const b2 = { id: 3, url: "https://b.example/" };
  const lost = { id: 4, url: "https://lost.example/" };
  const { restores, reopen } = matchRestores(
    [a, b1, b2, lost],
    [
      { tab: { sessionId: "s1", url: "https://b.example/" } },
      { window: { sessionId: "w1", tabs: [{ url: "https://a.example/" }] } },
      { tab: { sessionId: "s2", url: "https://a.example/" } },
      { tab: { sessionId: "s3", url: "https://b.example/" } },
      { tab: { sessionId: "s4", url: "https://b.example/" } },
      { tab: { url: "https://lost.example/" } },
    ],
  );
  assert.deepEqual(
    restores.map((restore) => [restore.sessionId, restore.entry.id]),
    [
      ["s1", 2],
      ["s2", 1],
      ["s3", 3],
    ],
  );
  assert.deepEqual(reopen, [lost]);
});

test("when the picks cover every copy of a URL, one copy stays out", () => {
  const { entries } = tabEntries(
    [
      { id: 1, url: "https://dup.example/" },
      { id: 2, url: "https://dup.example/" },
      { id: 3, url: "https://dup.example/" },
      { id: 4, url: "https://pair.example/" },
      { id: 5, url: "https://pair.example/" },
      { id: 6, url: "https://single.example/" },
    ],
    now,
    own,
  );
  const { close } = parseInsights(
    JSON.stringify({
      topics: [],
      close: [1, 2, 3, 4, 6].map((tab) => ({ tab, reason: "x" })),
    }),
    entries,
  );
  assert.deepEqual(close.map((pick) => pick.entry.id), [2, 3, 4, 6]);
});

test("grouping puts picks in Likely close, topics in their own groups, by window", () => {
  const e = (id) => ({ id });
  const topics = [
    { name: "Docs", tabs: [e(1), e(2), e(3)] },
    { name: "Code", tabs: [e(4), e(5), e(6), e(7), e(9)] },
  ];
  const picks = [e(3), e(5)];
  const open = [
    { id: 1, windowId: 10, groupId: -1 },
    { id: 2, windowId: 20, groupId: -1 },
    { id: 3, windowId: 10, groupId: -1 },
    { id: 4, windowId: 10, groupId: -1, pinned: true },
    { id: 5, windowId: 20, groupId: -1 },
    { id: 6, windowId: 10, groupId: 77 },
    { id: 7, windowId: 10 },
  ];
  assert.deepEqual(groupingPlan(topics, picks, open), [
    { title: "Likely close", color: "grey", collapsed: true, windowId: 10, tabIds: [3] },
    { title: "Likely close", color: "grey", collapsed: true, windowId: 20, tabIds: [5] },
    { title: "Docs", color: "blue", collapsed: false, windowId: 10, tabIds: [1] },
    { title: "Docs", color: "blue", collapsed: false, windowId: 20, tabIds: [2] },
    { title: "Code", color: "red", collapsed: false, windowId: 10, tabIds: [7] },
  ]);
});

test("undo moves tabs back in index order within each window", () => {
  assert.deepEqual(
    undoMoves([
      { id: 1, windowId: 2, index: 5 },
      { id: 2, windowId: 1, index: 3 },
      { id: 3, windowId: 2, index: 0 },
      { id: 4, windowId: 1, index: 1 },
    ]).map((move) => move.id),
    [4, 2, 3, 1],
  );
});
