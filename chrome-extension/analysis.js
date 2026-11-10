// The analysis and grouping that the side panel and the service worker share.
// Both run Gemini Nano through the Prompt API. The panel can also start the
// model download, which needs a click; the service worker can't.

import {
  MODEL_OPTIONS,
  RESPONSE_SCHEMA,
  SYSTEM_PROMPT,
  groupingPlan,
  parseInsights,
  tabEntries,
  tabSignature,
  userPrompt,
} from "./tab_insights.js";

export function createSession(model, monitor) {
  const options = {
    ...MODEL_OPTIONS,
    initialPrompts: [{ role: "system", content: SYSTEM_PROMPT }],
  };
  if (monitor) {
    options.monitor = monitor;
  }
  return model.create(options);
}

async function openGroups(api) {
  if (!api.tabGroups) {
    return [];
  }
  return api.tabGroups.query({});
}

// analyzeTabs asks the session about the open tabs. The result is plain data,
// so chrome.storage can keep it for the panel and the toolbar title.
export async function analyzeTabs(api, session, now = Date.now()) {
  const tabs = await api.tabs.query({});
  const titles = new Map((await openGroups(api)).map((group) => [group.id, group.title || ""]));
  const own = api.runtime.getURL("");
  const { entries, total } = tabEntries(tabs, now, own, titles);
  const result = {
    at: now,
    total,
    read: entries.length,
    seconds: 0,
    signature: tabSignature(tabs, own),
    insights: { topics: [], close: [] },
  };
  if (entries.length === 0) {
    return result;
  }
  const started = Date.now();
  const answer = await session.prompt(userPrompt(entries), {
    responseConstraint: RESPONSE_SCHEMA,
  });
  result.seconds = (Date.now() - started) / 1000;
  result.insights = parseInsights(answer, entries);
  return result;
}

// applyGroups makes or extends the tab groups for the topics and the picks.
// saved holds where each grouped tab was, for undo.
export async function applyGroups(api, topics, picks) {
  const open = await api.tabs.query({});
  const plan = groupingPlan(topics, picks, open, await openGroups(api));
  const where = new Map(open.map((tab) => [tab.id, { id: tab.id, windowId: tab.windowId, index: tab.index }]));
  const saved = plan.flatMap((group) => group.tabIds.map((id) => where.get(id)));
  for (const { title, color, collapsed, windowId, tabIds, groupId } of plan) {
    if (typeof groupId === "number") {
      await api.tabs.group({ groupId, tabIds });
    } else {
      const created = await api.tabs.group({ tabIds, createProperties: { windowId } });
      await api.tabGroups.update(created, { title, color, collapsed });
    }
  }
  return { saved, groups: new Set(plan.map((group) => group.title)).size };
}
