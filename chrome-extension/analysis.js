// The analysis and grouping that the side panel and the service worker share.
// Both run Gemini Nano through the Prompt API. The panel can also start the
// model download, which needs a click; the service worker can't.

import {
  MAX_TOPICS,
  MODEL_OPTIONS,
  RESPONSE_SCHEMA,
  SPLIT_SCHEMA,
  SYSTEM_PROMPT,
  groupingPlan,
  parseInsights,
  splitPrompt,
  splitTopic,
  tabEntries,
  tabSignature,
  topicLimit,
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
  // A clone taken before the first prompt holds only the system prompt, so
  // each split starts from a clean context instead of the whole first answer.
  const base = typeof session.clone === "function" ? await session.clone() : null;
  try {
    const answer = await session.prompt(userPrompt(entries), {
      responseConstraint: RESPONSE_SCHEMA,
    });
    result.insights = parseInsights(answer, entries);
    result.insights.topics = await splitTopics(base || session, result.insights.topics, topicLimit(entries.length));
  } finally {
    if (base) {
      base.destroy();
    }
  }
  result.seconds = (Date.now() - started) / 1000;
  return result;
}

async function askSplit(base, topic, limit) {
  const session = typeof base.clone === "function" ? await base.clone() : base;
  try {
    return await session.prompt(splitPrompt(topic.name, topic.tabs, limit), {
      responseConstraint: SPLIT_SCHEMA,
    });
  } catch (error) {
    console.error(error);
    return null;
  } finally {
    if (session !== base) {
      session.destroy();
    }
  }
}

// splitTopics asks the model to split each topic over the limit, and falls
// back to splitting by site when its answer doesn't.
async function splitTopics(base, topics, limit) {
  const result = [];
  for (const topic of topics) {
    if (topic.tabs.length <= limit) {
      result.push(topic);
    } else {
      result.push(...splitTopic(topic, await askSplit(base, topic, limit), limit));
    }
  }
  return result.slice(0, MAX_TOPICS);
}

// applyGroups makes or extends the tab groups for the topics and the picks.
// saved holds where each grouped tab was, for undo.
export async function applyGroups(api, topics, picks) {
  const open = await api.tabs.query({});
  const plan = groupingPlan(topics, picks, open, await openGroups(api));
  const where = new Map(open.map((tab) => [tab.id, { id: tab.id, windowId: tab.windowId, index: tab.index }]));
  // A tab can close between the plan and the click, so drop ids that are no
  // longer open rather than saving undefined for undo.
  const saved = plan.flatMap((group) => group.tabIds.map((id) => where.get(id)).filter(Boolean));
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
