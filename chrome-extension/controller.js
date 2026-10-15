import {
  BADGE_COLOR,
  BADGE_TEXT_COLOR,
  actionTitle,
  badgeText,
  duplicateTabIds,
} from "./duplicates.js";

// Chrome 150 added the "tab" context. Older Chrome rejects it, and the
// toolbar button still closes the same tabs.
const MENU_ID = "close-duplicates";

function errorText(error) {
  if (error && typeof error.message === "string") {
    return error.message;
  }
  return String(error);
}

function createMenuSync(api) {
  let menuUnsupported = false;
  return async function syncMenu(count) {
    if (!api.contextMenus || menuUnsupported) {
      return;
    }
    const title = actionTitle(count);
    const visible = count > 0;
    try {
      await api.contextMenus.update(MENU_ID, { title, visible });
      return;
    } catch (error) {
      if (!errorText(error).includes("Cannot find menu item")) {
        console.error(error);
        return;
      }
    }
    try {
      await api.contextMenus.create({
        id: MENU_ID,
        title,
        contexts: ["tab"],
        visible,
      });
    } catch (error) {
      const message = errorText(error);
      if (message.includes("duplicate id")) {
        return;
      }
      menuUnsupported = true;
      console.error(error);
    }
  };
}

async function showCount(api, count, syncMenu) {
  await api.action.setBadgeBackgroundColor({ color: BADGE_COLOR });
  await api.action.setBadgeTextColor({ color: BADGE_TEXT_COLOR });
  await api.action.setBadgeText({ text: badgeText(count) });
  await api.action.setTitle({ title: actionTitle(count) });
  await syncMenu(count);
}

export function start(api) {
  const syncMenu = createMenuSync(api);
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
      await showCount(api, duplicateTabIds(tabs).length, syncMenu);
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
      await showCount(api, duplicateTabIds(after).length, syncMenu);
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
  if (api.contextMenus) {
    api.contextMenus.onClicked.addListener((info) => {
      if (info && info.menuItemId === MENU_ID) {
        return closeDuplicates();
      }
      return Promise.resolve();
    });
  }
  return refresh();
}
