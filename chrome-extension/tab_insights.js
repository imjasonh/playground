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
  "Then pick tabs that are probably safe to close: stale tabs, finished tasks, empty new tab pages, search results, login pages, and tabs that show the same page as another tab.",
  "Never pick a tab flagged pinned, active, or audio.",
  "Refer to tabs only by their numbers. Give each pick a reason of at most 12 words.",
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
// picks to close. The result keeps window and tab order.
export function tabEntries(tabs, now, skipPrefix) {
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
        title: titleText(tab.title, where),
        location: where,
        age: used > 0 ? formatAge(Math.max(0, now - used)) : "",
        pinned: tab.pinned === true,
        active: tab.active === true,
        audible: tab.audible === true,
      };
    }),
  };
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
  return { topics, close };
}

export function closeLabel(count) {
  if (count === 1) {
    return "Close 1 tab";
  }
  return `Close ${count} tabs`;
}
