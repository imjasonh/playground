import { decodeBase64, menuTitle, textToCopy } from "./base64.js";
import {
  BADGE_COLOR,
  BADGE_TEXT_COLOR,
  actionTitle,
  badgeText,
  duplicateTabIds,
} from "./duplicates.js";

// Chrome 150 added the "tab" context. Older Chrome rejects it, and the
// toolbar button still closes the same tabs. The selection item is separate.
// It stays hidden until the highlighted text is base64. Chrome builds the
// menu from items that already exist, so the content script reports the
// selection before the right-click.
const MENU_ID = "close-duplicates";
const DECODE_ID = "decode-base64";
const HIDDEN_DECODE_TITLE = "Decoded";

function errorText(error) {
  if (error && typeof error.message === "string") {
    return error.message;
  }
  return String(error);
}

function frameKey(sender) {
  let tabId = "none";
  let frameId = "0";
  if (sender && sender.tab && typeof sender.tab.id === "number") {
    tabId = String(sender.tab.id);
  }
  if (sender && typeof sender.frameId === "number") {
    frameId = String(sender.frameId);
  }
  return `${tabId}:${frameId}`;
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

function createDecodeSync(api) {
  let unsupported = false;
  let menuTail = Promise.resolve();

  function enqueueMenu(task) {
    const run = menuTail.then(task);
    const settled = run.then(
      () => {},
      (error) => {
        console.error(error);
      },
    );
    menuTail = settled;
    return settled;
  }

  async function writeDecodeMenu(visible, title) {
    if (!api.contextMenus || unsupported) {
      return;
    }
    try {
      await api.contextMenus.update(DECODE_ID, { title, visible });
      return;
    } catch (error) {
      if (!errorText(error).includes("Cannot find menu item")) {
        console.error(error);
        return;
      }
    }
    if (!visible) {
      return;
    }
    try {
      await api.contextMenus.create({
        id: DECODE_ID,
        title,
        contexts: ["selection"],
        visible,
      });
    } catch (error) {
      const message = errorText(error);
      if (message.includes("duplicate id")) {
        await api.contextMenus.update(DECODE_ID, { title, visible });
        return;
      }
      unsupported = true;
      console.error(error);
    }
  }

  function setDecodeMenu(visible, title) {
    return enqueueMenu(() => writeDecodeMenu(visible, title));
  }

  function ensureDecodeMenu() {
    return enqueueMenu(async () => {
      if (!api.contextMenus || unsupported) {
        return;
      }
      try {
        await api.contextMenus.create({
          id: DECODE_ID,
          title: HIDDEN_DECODE_TITLE,
          contexts: ["selection"],
          visible: false,
        });
      } catch (error) {
        const message = errorText(error);
        if (message.includes("duplicate id")) {
          return;
        }
        unsupported = true;
        console.error(error);
      }
    });
  }

  return { setDecodeMenu, ensureDecodeMenu };
}

async function copyText(api, text) {
  const offscreen = api.offscreen;
  if (!offscreen || typeof offscreen.createDocument !== "function") {
    throw new Error("clipboard offscreen API is missing");
  }
  let open = false;
  if (typeof offscreen.hasDocument === "function") {
    open = await offscreen.hasDocument();
  }
  if (!open) {
    try {
      await offscreen.createDocument({
        url: "offscreen.html",
        reasons: ["CLIPBOARD"],
        justification: "Copy decoded base64 text to the clipboard.",
      });
    } catch (error) {
      const message = errorText(error);
      if (!message.includes("Only a single offscreen")) {
        throw error;
      }
    }
  }
  await api.runtime.sendMessage({
    target: "offscreen-clipboard",
    type: "copy",
    text,
  });
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
  const decodeMenu = createDecodeSync(api);
  let tail = Promise.resolve();
  let selectionTail = Promise.resolve();
  let owner = null;
  let pending = null;

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

  function enqueueSelection(task) {
    const run = selectionTail.then(task);
    const settled = run.then(
      () => {},
      (error) => {
        console.error(error);
      },
    );
    selectionTail = settled;
    return settled;
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

  function applySelection(text, key) {
    const decoded = decodeBase64(text);
    let title = null;
    if (decoded !== null) {
      title = menuTitle(decoded);
    }
    if (title === null) {
      // Another frame's empty selection must not clear a decode this frame
      // still owns. After the service worker restarts, nothing owns the item
      // Chrome restored, so a selection that is not base64 hides it.
      if (owner !== null && owner !== key) {
        return Promise.resolve();
      }
      owner = null;
      pending = null;
      return decodeMenu.setDecodeMenu(false, HIDDEN_DECODE_TITLE);
    }
    owner = key;
    pending = decoded;
    return decodeMenu.setDecodeMenu(true, title);
  }

  function copyDecoded(info) {
    let selectionText = "";
    if (info && typeof info.selectionText === "string") {
      selectionText = info.selectionText;
    }
    const text = textToCopy(selectionText, pending);
    if (text === null) {
      return Promise.resolve();
    }
    return copyText(api, text).then(
      () => {},
      (error) => {
        console.error(error);
      },
    );
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
  if (api.runtime.onMessage) {
    api.runtime.onMessage.addListener((message, sender, sendResponse) => {
      if (!message || message.type !== "selection" || message.target) {
        return;
      }
      const text = typeof message.text === "string" ? message.text : "";
      const key = frameKey(sender);
      if (typeof sendResponse === "function") {
        sendResponse({ ok: true });
      }
      return enqueueSelection(() => applySelection(text, key));
    });
  }
  if (api.contextMenus) {
    api.contextMenus.onClicked.addListener((info) => {
      if (info && info.menuItemId === MENU_ID) {
        return closeDuplicates();
      }
      if (info && info.menuItemId === DECODE_ID) {
        return copyDecoded(info);
      }
      return Promise.resolve();
    });
  }
  return decodeMenu.ensureDecodeMenu().then(() => refresh());
}
