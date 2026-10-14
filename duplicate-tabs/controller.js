import {
  BADGE_COLOR,
  BADGE_TEXT_COLOR,
  actionTitle,
  badgeText,
  duplicateTabIds,
} from "./duplicates.js";

async function showCount(api, count) {
  await api.action.setBadgeBackgroundColor({ color: BADGE_COLOR });
  await api.action.setBadgeTextColor({ color: BADGE_TEXT_COLOR });
  await api.action.setBadgeText({ text: badgeText(count) });
  await api.action.setTitle({ title: actionTitle(count) });
}

export function start(api) {
  let tail = Promise.resolve();

  function enqueue(task) {
    const run = tail.then(task);
    tail = run.then(
      (value) => value,
      (error) => {
        console.error(error);
        return error;
      },
    );
    return run;
  }

  function refresh() {
    return enqueue(async () => {
      const tabs = await api.tabs.query({});
      await showCount(api, duplicateTabIds(tabs).length);
    });
  }

  function closeDuplicates() {
    return enqueue(async () => {
      const tabs = await api.tabs.query({});
      const ids = duplicateTabIds(tabs);
      if (ids.length > 0) {
        await api.tabs.remove(ids);
      }
      const after = await api.tabs.query({});
      await showCount(api, duplicateTabIds(after).length);
      return ids;
    });
  }

  function onTabUpdated(tabId, changeInfo) {
    if (typeof tabId === "number" && (changeInfo.url || changeInfo.status === "complete")) {
      return refresh();
    }
    return Promise.resolve();
  }

  api.runtime.onInstalled.addListener(() => refresh());
  api.runtime.onStartup.addListener(() => refresh());
  api.tabs.onCreated.addListener(() => refresh());
  api.tabs.onRemoved.addListener(() => refresh());
  api.tabs.onReplaced.addListener(() => refresh());
  api.tabs.onAttached.addListener(() => refresh());
  api.tabs.onDetached.addListener(() => refresh());
  api.tabs.onUpdated.addListener(onTabUpdated);
  api.action.onClicked.addListener(() => closeDuplicates());
  return refresh();
}
