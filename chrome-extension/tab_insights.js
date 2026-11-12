// Tab insights asks Chrome's built-in model, through the Prompt API, to group
// open tabs by topic and to pick tabs to close. The model reads each tab's
// title, host and path, and how long ago it was used. It never reads page
// content, the query string, or the hash. It answers with the tab numbers
// from the prompt, and parseInsights maps those back to tabs. A pick for a
// pinned, active, or audible tab is dropped, and a tab not used in a week is
// added, whatever the model says. A topic over topicLimit is split again.

import { tabUrl } from "./duplicates.js";

export const MAX_TABS = 50;
export const MAX_TOPICS = 16;
export const MAX_CLOSE = 20;
// A topic is split when it holds more than a quarter of the tabs read, but a
// topic of this many tabs or fewer is never split.
const MIN_SPLIT = 8;
const MAX_SPLIT_GROUPS = 6;
// A tab not used for this long is a pick whatever the model says.
export const STALE_MS = 7 * 24 * 60 * 60 * 1000;
const DAY_MS = 24 * 60 * 60 * 1000;
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
  "Group the tabs into topics with short, specific names, such as a project, a repository, or a subject. Avoid broad names like Development, Work, or Research.",
  "Keep each topic small. When many tabs share a theme, split them into several topics, for example one per repository or project. A tab belongs to at most one topic.",
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

export const SPLIT_SCHEMA = {
  type: "object",
  properties: {
    groups: RESPONSE_SCHEMA.properties.topics,
  },
  required: ["groups"],
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
        idle: used > 0 ? Math.max(0, now - used) : 0,
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

// topicLimit is the most tabs a topic may hold before it is split. Three
// pull requests among 50 tabs stay one topic; 40 among 40 don't.
export function topicLimit(total) {
  return Math.max(MIN_SPLIT, Math.ceil(total / 4));
}

export function userPrompt(entries) {
  const limit = topicLimit(entries.length);
  return `${tabCount(entries.length)}. Put at most ${limit} tabs in a topic.\nTabs:\n${entries.map(tabLine).join("\n")}`;
}

// splitPrompt asks for a topic that came back too big to be split. The tabs
// are numbered from 1 again, so parseSplit takes the same entries.
export function splitPrompt(name, entries, limit) {
  const lines = entries.map((entry, index) => tabLine({ ...entry, number: index + 1 }));
  return [
    `These ${entries.length} tabs were grouped as "${name}", which is too broad.`,
    `Split them into 2 to ${MAX_SPLIT_GROUPS} smaller groups by repository, project, or subject, with short, specific names.`,
    `Put at most ${limit} tabs in a group. A tab belongs to at most one group. Refer to tabs only by their numbers.`,
    "Tabs:",
    ...lines,
  ].join("\n");
}

// parseInsights reads the model's JSON answer. Numbers that are not in the
// prompt are dropped, a tab is listed once per section, and empty topics go.
function readJson(text) {
  try {
    return JSON.parse(text);
  } catch {
    throw new Error("The model's answer was not JSON.");
  }
}

function readTopics(list, byNumber) {
  const topics = [];
  const grouped = new Set();
  for (const topic of Array.isArray(list) ? list : []) {
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
  return topics;
}

export function parseInsights(text, entries) {
  const answer = readJson(text);
  const byNumber = new Map(entries.map((entry) => [entry.number, entry]));
  const topics = readTopics(answer?.topics, byNumber);
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
  return { topics, close: keepOneCopy(addStale(close, entries), entries) };
}

// addStale adds the tabs not used in STALE_MS that the model didn't pick,
// oldest first. Age is a fact the small model weighs unevenly, so it is
// applied here instead of trusted to the prompt.
function addStale(close, entries) {
  const picked = new Set(close.map((pick) => pick.entry.number));
  const stale = entries
    .filter((entry) => entry.idle >= STALE_MS && !isProtected(entry) && !picked.has(entry.number))
    .sort((left, right) => right.idle - left.idle);
  const result = [...close];
  for (const entry of stale) {
    if (result.length >= MAX_CLOSE) {
      break;
    }
    result.push({ entry, reason: `Not used in ${Math.floor(entry.idle / DAY_MS)} days.` });
  }
  return result;
}

// parseSplit reads the answer to splitPrompt. rest holds the tabs no group
// took.
export function parseSplit(text, entries) {
  const answer = readJson(text);
  const byNumber = new Map(entries.map((entry, index) => [index + 1, entry]));
  const groups = readTopics(answer?.groups, byNumber);
  const taken = new Set(groups.flatMap((group) => group.tabs));
  return { groups, rest: entries.filter((entry) => !taken.has(entry)) };
}

function siteParts(url) {
  try {
    const parsed = new URL(url);
    const host = parsed.host.replace(/^www\./, "");
    return [host || parsed.protocol, ...parsed.pathname.split("/").filter((part) => part !== "")];
  } catch {
    return [url];
  }
}

// splitBySite splits a topic by host, then by the first path segment, then
// by the second, using the shallowest level that gives more than one bucket.
// github.com/org/repo/pull/1 splits by repository that way. Buckets of one
// tab go back into a group with the topic's name.
export function splitBySite(topic) {
  for (let depth = 1; depth <= 3; depth += 1) {
    const buckets = new Map();
    for (const entry of topic.tabs) {
      const key = siteParts(entry.url).slice(0, depth).join("/");
      const bucket = buckets.get(key);
      if (bucket) {
        bucket.push(entry);
      } else {
        buckets.set(key, [entry]);
      }
    }
    if (buckets.size < 2) {
      continue;
    }
    const groups = [];
    const rest = [];
    for (const [key, tabs] of buckets) {
      if (tabs.length > 1) {
        groups.push({ name: clip(key.split("/").at(-1), MAX_TOPIC_NAME), tabs });
      } else {
        rest.push(...tabs);
      }
    }
    if (groups.length === 0) {
      return [topic];
    }
    if (rest.length > 0) {
      groups.push({ name: topic.name, tabs: rest });
    }
    return groups;
  }
  return [topic];
}

// splitTopic turns one topic over the limit into smaller ones. It uses the
// model's split when that gives at least two groups, and splits by site any
// group still over the limit, or the whole topic when the model's answer is
// missing or didn't split it. Groups with the same name are merged.
export function splitTopic(topic, answer, limit) {
  let groups = [];
  let rest = topic.tabs;
  if (typeof answer === "string") {
    try {
      ({ groups, rest } = parseSplit(answer, topic.tabs));
    } catch {
      groups = [];
    }
  }
  if (groups.length < 2) {
    groups = [];
    rest = topic.tabs;
  }
  if (rest.length > 0) {
    groups.push({ name: topic.name, tabs: rest });
  }
  const split = groups.flatMap((group) => (group.tabs.length > limit ? splitBySite(group) : [group]));
  const byName = new Map();
  for (const group of split) {
    const key = group.name.toLowerCase();
    const same = byName.get(key);
    if (same) {
      same.tabs.push(...group.tabs);
    } else {
      byName.set(key, { name: group.name, tabs: [...group.tabs] });
    }
  }
  return [...byName.values()];
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
