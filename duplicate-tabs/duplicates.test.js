import assert from "node:assert/strict";
import test from "node:test";

import { actionTitle, badgeText, duplicateTabIds, tabUrl } from "./duplicates.js";

test("tabUrl prefers a real URL over a pending navigation", () => {
  assert.equal(tabUrl({ url: "https://example.com/a", pendingUrl: "https://example.com/b" }), "https://example.com/a");
  assert.equal(tabUrl({ url: "about:blank", pendingUrl: "https://example.com/b" }), "https://example.com/b");
  assert.equal(tabUrl({ url: "", pendingUrl: "https://example.com/b" }), "https://example.com/b");
  assert.equal(tabUrl({}), "");
  assert.equal(tabUrl(null), "");
});

test("unique URLs close nothing", () => {
  const ids = duplicateTabIds([
    { id: 1, url: "https://example.com/a" },
    { id: 2, url: "https://example.com/b" },
  ]);
  assert.deepEqual(ids, []);
});

test("exact URL match keeps the active tab and closes the other copies", () => {
  const ids = duplicateTabIds([
    { id: 1, url: "https://example.com/a", lastAccessed: 10 },
    { id: 2, url: "https://example.com/a", active: true, lastAccessed: 5 },
    { id: 3, url: "https://example.com/a", lastAccessed: 30 },
    { id: 4, url: "https://example.com/b" },
  ]);
  assert.deepEqual(ids, [1, 3]);
});

test("a pinned tab is kept ahead of the active tab", () => {
  const ids = duplicateTabIds([
    { id: 1, url: "https://example.com/a", pinned: true, lastAccessed: 1 },
    { id: 2, url: "https://example.com/a", active: true, lastAccessed: 50 },
    { id: 3, url: "https://example.com/a", pinned: true, lastAccessed: 9 },
  ]);
  assert.deepEqual(ids, [1, 2]);
});

test("the most recently used tab is kept when none are pinned or active", () => {
  const ids = duplicateTabIds([
    { id: 4, url: "https://example.com/a", lastAccessed: 10 },
    { id: 5, url: "https://example.com/a", lastAccessed: 40 },
    { id: 6, url: "https://example.com/a", lastAccessed: 20 },
  ]);
  assert.deepEqual(ids, [4, 6]);
});

test("a lower id wins a tie", () => {
  const ids = duplicateTabIds([
    { id: 8, url: "https://example.com/a", lastAccessed: 10 },
    { id: 3, url: "https://example.com/a", lastAccessed: 10 },
  ]);
  assert.deepEqual(ids, [8]);
});

test("hash and trailing slash stay part of the URL", () => {
  const ids = duplicateTabIds([
    { id: 1, url: "https://example.com/a" },
    { id: 2, url: "https://example.com/a/" },
    { id: 3, url: "https://example.com/a#one" },
    { id: 4, url: "https://example.com/a#one" },
  ]);
  assert.deepEqual(ids, [4]);
});

test("blank tabs are not grouped, and a pending URL is", () => {
  const ids = duplicateTabIds([
    { id: 1, url: "" },
    { id: 2 },
    { id: 3, url: "about:blank", pendingUrl: "https://example.com/a" },
    { id: 4, url: "https://example.com/a", active: true },
  ]);
  assert.deepEqual(ids, [3]);
});

test("duplicates in different windows count together", () => {
  const ids = duplicateTabIds([
    { id: 1, url: "https://example.com/a", windowId: 1, active: true, lastAccessed: 5 },
    { id: 2, url: "https://example.com/a", windowId: 2, active: true, lastAccessed: 5 },
  ]);
  assert.deepEqual(ids, [2]);
});

test("badge text is the number of tabs the click will close", () => {
  assert.equal(badgeText(0), "");
  assert.equal(badgeText(1), "1");
  assert.equal(badgeText(12), "12");
  assert.equal(badgeText(999), "999");
  assert.equal(badgeText(1000), "999+");
  assert.equal(actionTitle(0), "No duplicate tabs");
  assert.equal(actionTitle(1), "Close 1 duplicate tab");
  assert.equal(actionTitle(2), "Close 2 duplicate tabs");
});
