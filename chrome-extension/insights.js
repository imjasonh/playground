import { analyzeTabs, applyGroups, createSession } from "./analysis.js";
import { DEFAULT_SETTINGS } from "./background_insights.js";
import {
  MODEL_OPTIONS,
  closableIds,
  closeLabel,
  formatAge,
  matchRestores,
  tabCount,
  tabSignature,
  undoMoves,
  withoutTabs,
} from "./tab_insights.js";

// A saved analysis of the same tabs is shown instead of a new run when it is
// younger than this.
const SAVED_MAX_AGE_MS = 2 * 60 * 60 * 1000;

const analyzeButton = document.getElementById("analyze");
const statusLine = document.getElementById("status");
const download = document.getElementById("download");
const closeSection = document.getElementById("close-section");
const closeList = document.getElementById("close-list");
const closeEmpty = document.getElementById("close-empty");
const closeButton = document.getElementById("close");
const topicsSection = document.getElementById("topics-section");
const topicsBox = document.getElementById("topics");
const groupRow = document.getElementById("group-row");
const groupButton = document.getElementById("group");
const undoButtons = [document.getElementById("undo"), document.getElementById("group-undo")];
const backgroundBox = document.getElementById("background");
const autoGroupBox = document.getElementById("auto-group");

let insights = { topics: [], close: [] };
let analysis = 0;
let busy = false;
// A close pushes the tabs it closed and the insights from before it. Group
// tabs pushes where each tab it grouped was.
const undoStack = [];

function errorText(error) {
  if (error && typeof error.message === "string") {
    return error.message;
  }
  return String(error);
}

function setStatus(text, isError = false) {
  statusLine.textContent = text;
  statusLine.classList.toggle("error", isError);
}

// The Prompt API is a window global with no extension permission. It is not
// exposed to workers, so the model runs here and not in the service worker.
async function modelState() {
  if (typeof LanguageModel === "undefined") {
    return {
      label: "Analyze tabs",
      enabled: false,
      status: "This Chrome has no Prompt API. Tab insights needs desktop Chrome 138 or later.",
      error: true,
    };
  }
  let availability;
  try {
    availability = await LanguageModel.availability(MODEL_OPTIONS);
  } catch (error) {
    return { label: "Analyze tabs", enabled: false, status: errorText(error), error: true };
  }
  switch (availability) {
    case "available":
      return { label: "Analyze tabs", enabled: true, ready: true, status: "Built-in model ready." };
    case "downloadable":
      return {
        label: "Download model and analyze",
        enabled: true,
        status: "Built-in model not downloaded.",
      };
    case "downloading":
      return { label: "Analyze tabs", enabled: true, status: "Built-in model downloading." };
    case "unavailable":
      return {
        label: "Analyze tabs",
        enabled: false,
        status: "Chrome's built-in model is not available on this device.",
        error: true,
      };
    default:
      return { label: "Analyze tabs", enabled: true, status: `Built-in model: ${availability}.` };
  }
}

async function refreshButton(withStatus) {
  const state = await modelState();
  analyzeButton.textContent = state.label;
  analyzeButton.disabled = !state.enabled || busy;
  if (withStatus) {
    setStatus(state.status, state.error === true);
  }
  return state;
}

function setBusy(value) {
  busy = value;
  analyzeButton.disabled = value;
  for (const button of undoButtons) {
    button.disabled = value;
  }
  closeButton.disabled = value;
  groupButton.disabled = value;
  if (!value) {
    updateCloseButton();
  }
}

function updateUndo() {
  for (const button of undoButtons) {
    button.hidden = undoStack.length === 0;
  }
}

async function focusTab(entry) {
  try {
    await chrome.tabs.update(entry.id, { active: true });
    if (typeof entry.windowId === "number") {
      await chrome.windows.update(entry.windowId, { focused: true });
    }
  } catch (error) {
    setStatus(errorText(error), true);
  }
}

function tabButton(entry) {
  const button = document.createElement("button");
  button.type = "button";
  button.className = "tab";
  button.textContent = entry.title;
  button.title = entry.location;
  button.addEventListener("click", () => focusTab(entry));
  return button;
}

function checkedIds() {
  return [...closeList.querySelectorAll("input:checked")].map((input) => Number(input.value));
}

function updateCloseButton() {
  const count = checkedIds().length;
  closeButton.textContent = closeLabel(count);
  closeButton.disabled = count === 0 || busy;
}

function render() {
  closeList.replaceChildren();
  for (const { entry, reason } of insights.close) {
    const input = document.createElement("input");
    input.type = "checkbox";
    input.checked = true;
    input.value = String(entry.id);
    input.addEventListener("change", updateCloseButton);
    const label = document.createElement("label");
    label.append(input, tabButton(entry));
    if (reason !== "") {
      const why = document.createElement("span");
      why.className = "reason";
      why.textContent = reason;
      label.append(why);
    }
    const item = document.createElement("li");
    item.append(label);
    closeList.append(item);
  }
  closeEmpty.hidden = insights.close.length > 0;
  closeButton.hidden = insights.close.length === 0;
  updateCloseButton();
  closeSection.hidden = false;

  topicsBox.replaceChildren();
  for (const topic of insights.topics) {
    const heading = document.createElement("h3");
    const count = document.createElement("span");
    count.className = "count";
    count.textContent = ` · ${topic.tabs.length}`;
    heading.append(topic.name, count);
    const list = document.createElement("ul");
    for (const entry of topic.tabs) {
      const item = document.createElement("li");
      item.append(tabButton(entry));
      list.append(item);
    }
    topicsBox.append(heading, list);
  }
  topicsSection.hidden = insights.topics.length === 0;
  groupRow.hidden = insights.topics.length === 0 && insights.close.length === 0;
}

function clearResults() {
  insights = { topics: [], close: [] };
  closeSection.hidden = true;
  topicsSection.hidden = true;
  groupRow.hidden = true;
}

function checkedPicks() {
  const wanted = new Set(checkedIds());
  return insights.close.filter((pick) => wanted.has(pick.entry.id)).map((pick) => pick.entry);
}

async function analyze() {
  setBusy(true);
  clearResults();
  analysis += 1;
  let session = null;
  try {
    setStatus("Starting the built-in model…");
    // createSession is the first await so a download keeps the click's
    // activation.
    session = await createSession(LanguageModel, (monitor) => {
      monitor.addEventListener("downloadprogress", (event) => {
        download.hidden = false;
        download.value = event.loaded;
        setStatus(`Downloading the built-in model: ${Math.round(event.loaded * 100)}%`);
      });
    });
    download.hidden = true;
    setStatus("Reading tabs…");
    const result = await analyzeTabs(chrome, session);
    await chrome.storage.local.set({ insights: result });
    if (result.read === 0) {
      setStatus("No tabs to read.");
      return;
    }
    insights = result.insights;
    render();
    let read = tabCount(result.read);
    if (result.total > result.read) {
      read = `the ${result.read} oldest of ${result.total} tabs`;
    }
    let status = `Read ${read} on this device in ${result.seconds.toFixed(1)} s.`;
    if (autoGroupBox.checked) {
      const { saved } = await groupInto(insights.topics, checkedPicks());
      if (saved.length > 0) {
        status = `${status} Grouped ${tabCount(saved.length)}.`;
      }
    }
    setStatus(status);
  } catch (error) {
    setStatus(errorText(error), true);
  } finally {
    if (session) {
      session.destroy();
    }
    download.hidden = true;
    setBusy(false);
    updateUndo();
    await refreshButton(false);
  }
}

async function closeTabs(entries) {
  setBusy(true);
  try {
    const open = await chrome.tabs.query({});
    const ids = closableIds(entries.map((entry) => entry.id), open);
    if (ids.length === 0) {
      setStatus("Nothing to close. Pinned and active tabs stay open.");
      return;
    }
    const gone = new Set(ids);
    const closed = entries.filter((entry) => gone.has(entry.id));
    const before = insights;
    await chrome.tabs.remove(ids);
    undoStack.push({ kind: "close", closed, before, analysis });
    insights = withoutTabs(insights, gone);
    render();
    setStatus(`Closed ${tabCount(ids.length)}.`);
  } catch (error) {
    setStatus(errorText(error), true);
  } finally {
    setBusy(false);
    updateUndo();
  }
}

function closeChecked() {
  return closeTabs(checkedPicks());
}

async function reopen(entry) {
  try {
    return await chrome.tabs.create({ url: entry.url, windowId: entry.windowId, active: false });
  } catch {
    return chrome.tabs.create({ url: entry.url, active: false });
  }
}

// Restored tabs get new ids. The entries are shared by the suggestions and
// the topics, so updating them in place brings back the earlier panel.
async function undoClose(batch) {
  const recent = await chrome.sessions.getRecentlyClosed({ maxResults: chrome.sessions.MAX_SESSION_RESULTS });
  const plan = matchRestores(batch.closed, recent);
  for (const { sessionId, entry } of plan.restores) {
    const session = await chrome.sessions.restore(sessionId);
    if (session && session.tab) {
      entry.id = session.tab.id;
      entry.windowId = session.tab.windowId;
    }
  }
  for (const entry of plan.reopen) {
    const tab = await reopen(entry);
    entry.id = tab.id;
    entry.windowId = tab.windowId;
  }
  if (batch.analysis === analysis) {
    insights = batch.before;
    render();
  }
  setStatus(`Reopened ${tabCount(batch.closed.length)}.`);
}

// Group tabs only groups tabs that were in no group, so ungrouping them and
// moving each back to its index restores the tab strip. Empty groups go away.
async function undoGroup(batch) {
  const open = new Set((await chrome.tabs.query({})).map((tab) => tab.id));
  const saved = batch.saved.filter((tab) => open.has(tab.id));
  if (saved.length > 0) {
    await chrome.tabs.ungroup(saved.map((tab) => tab.id));
  }
  for (const { id, windowId, index } of undoMoves(saved)) {
    await chrome.tabs.move(id, { windowId, index });
  }
  setStatus(`Ungrouped ${tabCount(saved.length)}.`);
}

async function undo() {
  const batch = undoStack.pop();
  if (!batch) {
    return;
  }
  setBusy(true);
  try {
    if (batch.kind === "group") {
      await undoGroup(batch);
    } else {
      await undoClose(batch);
    }
  } catch (error) {
    setStatus(errorText(error), true);
  } finally {
    setBusy(false);
    updateUndo();
  }
}

async function groupInto(topics, picks) {
  const grouping = await applyGroups(chrome, topics, picks);
  if (grouping.saved.length > 0) {
    undoStack.push({ kind: "group", saved: grouping.saved });
  }
  updateUndo();
  return grouping;
}

async function groupTabs() {
  setBusy(true);
  try {
    const { saved, groups } = await groupInto(insights.topics, checkedPicks());
    if (saved.length === 0) {
      setStatus("Nothing to group. Pinned tabs and tabs already in a group stay as they are.");
    } else {
      setStatus(`Grouped ${tabCount(saved.length)} into ${groups === 1 ? "1 group" : `${groups} groups`}.`);
    }
  } catch (error) {
    setStatus(errorText(error), true);
  } finally {
    setBusy(false);
  }
}

// showSaved renders the last analysis when it covers the open tabs, so the
// panel doesn't wait for the model. A grouping the service worker made with
// that analysis joins the undo history.
async function showSaved() {
  const { insights: saved } = await chrome.storage.local.get("insights");
  const tabs = await chrome.tabs.query({});
  const signature = tabSignature(tabs, chrome.runtime.getURL(""));
  const current = saved && saved.signature === signature && Date.now() - saved.at < SAVED_MAX_AGE_MS;
  if (!current || saved.read === 0) {
    return false;
  }
  analysis += 1;
  insights = saved.insights;
  render();
  const age = formatAge(Date.now() - saved.at);
  setStatus(age === "now" ? "Analyzed just now." : `Analyzed ${age}.`);
  const { grouping } = await chrome.storage.local.get("grouping");
  if (grouping && grouping.at === saved.at) {
    undoStack.push({ kind: "group", saved: grouping.saved });
    await chrome.storage.local.remove("grouping");
    updateUndo();
  }
  return true;
}

async function loadSettings() {
  const settings = await chrome.storage.local.get(DEFAULT_SETTINGS);
  backgroundBox.checked = settings.background;
  autoGroupBox.checked = settings.autoGroup;
}

analyzeButton.addEventListener("click", analyze);
closeButton.addEventListener("click", closeChecked);
groupButton.addEventListener("click", groupTabs);
for (const button of undoButtons) {
  button.addEventListener("click", undo);
}
backgroundBox.addEventListener("change", () => chrome.storage.local.set({ background: backgroundBox.checked }));
autoGroupBox.addEventListener("change", () => chrome.storage.local.set({ autoGroup: autoGroupBox.checked }));

async function openPanel() {
  await loadSettings();
  const state = await refreshButton(true);
  if (await showSaved()) {
    return;
  }
  if (state.ready) {
    await analyze();
  }
}

openPanel().catch((error) => {
  setStatus(errorText(error), true);
});
