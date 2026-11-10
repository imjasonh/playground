// Tab insights asks Chrome's built-in model, through the Prompt API, to group
// open tabs by topic and to pick tabs to close. The model reads each tab's
// title, host and path, and how long ago it was used. It never reads page
// content, the query string, or the hash. It answers with the tab numbers
// from the prompt, and parseInsights maps those back to tabs. A pick for a
// pinned, active, or audible tab is dropped, whatever the model says.

import { tabUrl } from "./duplicates.js";

export const MAX_TABS = 50;
export const MAX_TOPICS = 8;
export const MAX_CLOSE = 20;
const MAX_TITLE = 80;
const MAX_LOCATION = 60;
const MAX_TOPIC_NAME = 40;
const MAX_REASON = 100;

export const MODEL_OPTIONS = {
  expectedInputs: [{ type: "text", languages: ["en"] }],
  expectedOutputs: [{ type: "text", languages: ["en"] }],
};

export const SYSTEM_PROMPT = [
  "You sort a person's open browser tabs.",
  "Each line is one tab: its number, how long ago it was last used, any flags, its title, and its URL without the query string.",
  "Group the tabs into a few topics with short names. A tab belongs to at most one topic.",
  "A tab flagged with a group is already in that group. Use the group's name as the topic for it, and reuse that name for similar tabs.",
  "Then pick the few tabs that are clearly safe to close. Most tabs should stay open.",
  "Good picks are empty new tab pages, tabs that show the same page as another tab, search results, and login pages. A tab not used for days may also be stale.",
  "Don't pick a tab used within the last hour unless it is one of those good picks.",
  "Never pick a tab flagged pinned, active, or audio.",
  "Refer to tabs only by their numbers. Give each pick a reason of at most 12 words. A reason must not mention tab numbers.",
].join("\n");

export const RESPONSE_SCHEMA = {
  type: "object",
  properties: {
    topics: {
      type: "array",
      items: {
        type: "object",
        properties: {
          name: { type: "string" },
          tabs: { type: "array", items: { type: "integer" } },
        },
        required: ["name", "tabs"],
      },
    },
    close: {
      type: "array",
      items: {
        type: "object",
        properties: {
          tab: { type: "integer" },
          reason: { type: "string" },
        },
        required: ["tab", "reason"],
      },
    },
  },
  required: ["topics", "close"],
};

function clip(text, max) {
  const flat = text.replace(/\s+/g, " ").trim();
  if (flat.length <= max) {
    return flat;
  }
  return `${flat.slice(0, max - 1)}…`;
}

function location(url) {
  let parsed;
  try {
    parsed = new URL(url);
  } catch {
    return clip(url.split(/[?#]/)[0], MAX_LOCATION);
  }
  if (parsed.protocol === "http:" || parsed.protocol === "https:") {
    return clip(`${parsed.host}${parsed.pathname}`, MAX_LOCATION);
  }
  parsed.search = "";
  parsed.hash = "";
  return clip(parsed.href, MAX_LOCATION);
}

// Chrome titles a page that has no <title> with its full URL, and some pages
// set a URL as the title. Those go through location so no query leaks.
function titleText(title, where) {
  if (typeof title !== "string" || title.trim() === "") {
    return where;
  }
  if (/^[a-z][a-z0-9+.-]*:\/\/\S*$/i.test(title.trim())) {
    return location(title.trim());
  }
  return clip(title, MAX_TITLE);
}

export function formatAge(ms) {
  const minutes = Math.floor(ms / 60000);
  if (minutes < 1) {
    return "now";
  }
  if (minutes < 60) {
    return `${minutes}m ago`;
  }
  const hours = Math.floor(minutes / 60);
  if (hours < 24) {
    return `${hours}h ago`;
  }
  return `${Math.floor(hours / 24)}d ago`;
}

// tabEntries picks the tabs the model reads and numbers them from 1. Tabs
// whose URL starts with skipPrefix (the side panel's own pages) are left out.
// Past MAX_TABS, the tabs used longest ago win, since those are the likely
// picks to close. The result keeps window and tab order. groupTitles maps a
// tab group id to its name, so the model can reuse the names.
export function tabEntries(tabs, now, skipPrefix, groupTitles = new Map()) {
  const candidates = [];
  for (const tab of tabs) {
    const url = tabUrl(tab);
    const usable = typeof tab.id === "number" && url !== "";
    if (usable && !(skipPrefix && url.startsWith(skipPrefix))) {
      candidates.push({ tab, url, order: candidates.length });
    }
  }
  let chosen = candidates;
  if (candidates.length > MAX_TABS) {
    chosen = [...candidates]
      .sort((left, right) => (Number(left.tab.lastAccessed) || 0) - (Number(right.tab.lastAccessed) || 0))
      .slice(0, MAX_TABS)
      .sort((left, right) => left.order - right.order);
  }
  return {
    total: candidates.length,
    entries: chosen.map(({ tab, url }, index) => {
      const used = Number(tab.lastAccessed);
      const where = location(url);
      return {
        number: index + 1,
        id: tab.id,
        windowId: tab.windowId,
        url,
        title: titleText(tab.title, where),
        location: where,
        age: used > 0 ? formatAge(Math.max(0, now - used)) : "",
        pinned: tab.pinned === true,
        active: tab.active === true,
        audible: tab.audible === true,
        group: clip(groupTitles.get(tab.groupId) || "", MAX_TOPIC_NAME),
      };
    }),
  };
}

// tabSignature changes when a tab opens, closes, or navigates, so the
// background job can skip a run when nothing changed. It skips the same
// pages tabEntries does.
export function tabSignature(tabs, skipPrefix) {
  return tabs
    .map((tab) => `${tab.id} ${tabUrl(tab)}`)
    .filter((line) => !(skipPrefix && line.split(" ")[1].startsWith(skipPrefix)))
    .sort()
    .join("\n");
}

export function isProtected(entry) {
  return entry.pinned || entry.active || entry.audible;
}

export function tabLine(entry) {
  const parts = [`${entry.number}.`];
  if (entry.age !== "") {
    parts.push(`[${entry.age}]`);
  }
  const flags = [];
  if (entry.pinned) {
    flags.push("pinned");
  }
  if (entry.active) {
    flags.push("active");
  }
  if (entry.audible) {
    flags.push("audio");
  }
  if (entry.group) {
    flags.push(`group: ${entry.group}`);
  }
  if (flags.length > 0) {
    parts.push(`(${flags.join(", ")})`);
  }
  parts.push(entry.title, "—", entry.location);
  return parts.join(" ");
}

export function userPrompt(entries) {
  return `Tabs:\n${entries.map(tabLine).join("\n")}`;
}

// parseInsights reads the model's JSON answer. Numbers that are not in the
// prompt are dropped, a tab is listed once per section, and empty topics go.
export function parseInsights(text, entries) {
  let answer;
  try {
    answer = JSON.parse(text);
  } catch {
    throw new Error("The model's answer was not JSON.");
  }
  const byNumber = new Map(entries.map((entry) => [entry.number, entry]));
  const topics = [];
  const grouped = new Set();
  for (const topic of Array.isArray(answer?.topics) ? answer.topics : []) {
    const name = typeof topic?.name === "string" ? clip(topic.name, MAX_TOPIC_NAME) : "";
    const tabs = [];
    for (const number of Array.isArray(topic?.tabs) ? topic.tabs : []) {
      const entry = byNumber.get(number);
      if (entry && !grouped.has(number)) {
        grouped.add(number);
        tabs.push(entry);
      }
    }
    if (name !== "" && tabs.length > 0 && topics.length < MAX_TOPICS) {
      topics.push({ name, tabs });
    }
  }
  const close = [];
  const picked = new Set();
  for (const pick of Array.isArray(answer?.close) ? answer.close : []) {
    const entry = byNumber.get(pick?.tab);
    if (entry && !isProtected(entry) && !picked.has(entry.number) && close.length < MAX_CLOSE) {
      picked.add(entry.number);
      const reason = typeof pick.reason === "string" ? clip(pick.reason, MAX_REASON) : "";
      close.push({ entry, reason });
    }
  }
  return { topics, close: keepOneCopy(close, entries) };
}

// keepOneCopy drops the first pick of a URL when the picks cover every open
// copy of it, so closing the picks never loses a page that had duplicates.
function keepOneCopy(close, entries) {
  const copies = new Map();
  for (const entry of entries) {
    copies.set(entry.url, (copies.get(entry.url) || 0) + 1);
  }
  const picks = new Map();
  for (const pick of close) {
    picks.set(pick.entry.url, (picks.get(pick.entry.url) || 0) + 1);
  }
  const spared = new Set();
  return close.filter((pick) => {
    const url = pick.entry.url;
    const all = copies.get(url) >= 2 && picks.get(url) === copies.get(url);
    if (all && !spared.has(url)) {
      spared.add(url);
      return false;
    }
    return true;
  });
}

export function closeLabel(count) {
  if (count === 1) {
    return "Close 1 tab";
  }
  return `Close ${count} tabs`;
}

export function tabCount(count) {
  return count === 1 ? "1 tab" : `${count} tabs`;
}

// closableIds keeps the wanted tabs that are still open and are not pinned
// or active now. Every window keeps its active tab, so a close never closes
// a window, and the side panel's window stays open.
export function closableIds(wanted, openTabs) {
  const want = new Set(wanted);
  return openTabs
    .filter((tab) => want.has(tab.id) && tab.pinned !== true && tab.active !== true)
    .map((tab) => tab.id);
}

export function withoutTabs(insights, gone) {
  return {
    close: insights.close.filter((pick) => !gone.has(pick.entry.id)),
    topics: insights.topics
      .map((topic) => ({ ...topic, tabs: topic.tabs.filter((entry) => !gone.has(entry.id)) }))
      .filter((topic) => topic.tabs.length > 0),
  };
}

// matchRestores pairs closed tabs with Recently Closed entries by URL, newest
// entry first, so undo restores each tab with its history. A closed tab with
// no matching entry is reopened from its URL instead. Window entries are
// skipped, since closableIds never closes a window.
export function matchRestores(closed, recent) {
  const waiting = new Map();
  for (const entry of closed) {
    const list = waiting.get(entry.url);
    if (list) {
      list.push(entry);
    } else {
      waiting.set(entry.url, [entry]);
    }
  }
  const restores = [];
  for (const session of recent) {
    const tab = session && session.tab;
    const list = tab && waiting.get(tab.url);
    if (list && list.length > 0 && typeof tab.sessionId === "string") {
      restores.push({ sessionId: tab.sessionId, entry: list.shift() });
    }
  }
  const reopen = closed.filter((entry) => !restores.some((restore) => restore.entry === entry));
  return { restores, reopen };
}

export const LIKELY_CLOSE = "Likely close";
const TOPIC_COLORS = ["blue", "red", "yellow", "green", "pink", "purple", "cyan", "orange"];
const NO_GROUP = -1;

// groupingPlan turns each topic into a Chrome tab group and the picks to
// close into a collapsed grey group. A pick leaves its topic's group. A
// group lives in one window, so each window gets its own copy and no tab
// moves. Tabs that are closed, pinned, or already in a group are left alone.
// When a window already has a group with the same name, the plan adds the
// tabs to it with its groupId, so repeated runs don't make copies.
export function groupingPlan(topics, picks, openTabs, groups = []) {
  const open = new Map(openTabs.map((tab) => [tab.id, tab]));
  const taken = new Set();
  const plan = [];
  function add(title, color, collapsed, entries) {
    const byWindow = new Map();
    for (const entry of entries) {
      const tab = open.get(entry.id);
      const free = tab && tab.pinned !== true && (tab.groupId === undefined || tab.groupId === NO_GROUP);
      if (free && !taken.has(tab.id)) {
        taken.add(tab.id);
        const ids = byWindow.get(tab.windowId);
        if (ids) {
          ids.push(tab.id);
        } else {
          byWindow.set(tab.windowId, [tab.id]);
        }
      }
    }
    for (const [windowId, tabIds] of byWindow) {
      const existing = groups.find((group) => group.windowId === windowId && group.title === title);
      if (existing) {
        plan.push({ title, windowId, tabIds, groupId: existing.id });
      } else {
        plan.push({ title, color, collapsed, windowId, tabIds });
      }
    }
  }
  add(LIKELY_CLOSE, "grey", true, picks);
  topics.forEach((topic, index) => {
    add(topic.name, TOPIC_COLORS[index % TOPIC_COLORS.length], false, topic.tabs);
  });
  return plan;
}

// undoMoves orders the saved tab positions so moving each tab back to its
// index, one at a time, restores the old order in every window.
export function undoMoves(saved) {
  return [...saved].sort((left, right) => left.windowId - right.windowId || left.index - right.index);
}
