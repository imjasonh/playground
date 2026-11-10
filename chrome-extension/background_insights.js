// The service worker analyzes tabs on a timer and a minute after tabs
// change, so a grouping plan is ready when the panel opens. The Prompt API
// works in an extension service worker without a click once the model is on
// the device. The job never starts the download, and it never groups tabs.

import { analyzeTabs, createSession } from "./analysis.js";
import { LIKELY_CLOSE, MODEL_OPTIONS, tabSignature } from "./tab_insights.js";

export const ALARM = "tab-insights";
// Recreating this alarm on every tab change pushes it back, so it fires once
// tabs have been quiet for a minute.
export const SOON_ALARM = "tab-insights-soon";
const PERIOD_MINUTES = 15;
const MAX_AGE_MS = 2 * 60 * 60 * 1000;
const NO_GROUP = -1;

export function startInsights(api, model) {
  let running = null;

  async function analyzeNow() {
    if (!model || (await model.availability(MODEL_OPTIONS)) !== "available") {
      return;
    }
    const tabs = await api.tabs.query({});
    const { insights: last } = await api.storage.local.get("insights");
    const unchanged = last && last.signature === tabSignature(tabs, api.runtime.getURL(""));
    if (unchanged && Date.now() - last.at < MAX_AGE_MS) {
      return;
    }
    const session = await createSession(model);
    let result;
    try {
      result = await analyzeTabs(api, session);
    } finally {
      session.destroy();
    }
    await api.storage.local.set({ insights: result });
  }

  function run() {
    if (!running) {
      running = analyzeNow()
        .catch((error) => {
          console.error(error);
        })
        .finally(() => {
          running = null;
        });
    }
    return running;
  }

  function soon() {
    return api.alarms.create(SOON_ALARM, { delayInMinutes: 1 });
  }

  // A tab you switch to is in use, so it stops being a pick and leaves the
  // Likely close group.
  async function spare(tabId) {
    const { insights } = await api.storage.local.get("insights");
    if (insights && insights.insights.close.some((pick) => pick.entry.id === tabId)) {
      insights.insights.close = insights.insights.close.filter((pick) => pick.entry.id !== tabId);
      await api.storage.local.set({ insights });
    }
    if (!api.tabGroups) {
      return;
    }
    const tab = await api.tabs.get(tabId);
    if (typeof tab.groupId !== "number" || tab.groupId === NO_GROUP) {
      return;
    }
    const group = await api.tabGroups.get(tab.groupId);
    if (group.title === LIKELY_CLOSE) {
      await api.tabs.ungroup(tabId);
    }
  }

  api.alarms.onAlarm.addListener((alarm) => {
    if (alarm.name === ALARM || alarm.name === SOON_ALARM) {
      return run();
    }
    return Promise.resolve();
  });
  api.tabs.onCreated.addListener(() => soon());
  api.tabs.onRemoved.addListener(() => soon());
  api.tabs.onUpdated.addListener((tabId, changeInfo) => {
    if (changeInfo && changeInfo.url) {
      return soon();
    }
    return Promise.resolve();
  });
  api.tabs.onActivated.addListener((info) =>
    spare(info.tabId).catch((error) => {
      console.error(error);
    }),
  );
  const ready = api.alarms.get(ALARM).then((alarm) => {
    if (!alarm) {
      return api.alarms.create(ALARM, { delayInMinutes: 1, periodInMinutes: PERIOD_MINUTES });
    }
    return undefined;
  });
  return { run, ready };
}
