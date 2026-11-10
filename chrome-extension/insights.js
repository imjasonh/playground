import {
  MODEL_OPTIONS,
  RESPONSE_SCHEMA,
  SYSTEM_PROMPT,
  closeLabel,
  parseInsights,
  tabEntries,
  userPrompt,
} from "./tab_insights.js";

const analyzeButton = document.getElementById("analyze");
const statusLine = document.getElementById("status");
const download = document.getElementById("download");
const closeSection = document.getElementById("close-section");
const closeList = document.getElementById("close-list");
const closeEmpty = document.getElementById("close-empty");
const closeButton = document.getElementById("close");
const topicsSection = document.getElementById("topics-section");
const topicsBox = document.getElementById("topics");

let insights = { topics: [], close: [] };

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
      return { label: "Analyze tabs", enabled: true, status: "Built-in model ready." };
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
  analyzeButton.disabled = !state.enabled;
  if (withStatus) {
    setStatus(state.status, state.error === true);
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
  closeButton.disabled = count === 0;
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
}

function clearResults() {
  insights = { topics: [], close: [] };
  closeSection.hidden = true;
  topicsSection.hidden = true;
}

async function analyze() {
  analyzeButton.disabled = true;
  clearResults();
  let session = null;
  try {
    setStatus("Starting the built-in model…");
    // create() is the first await so a download keeps the click's activation.
    session = await LanguageModel.create({
      ...MODEL_OPTIONS,
      initialPrompts: [{ role: "system", content: SYSTEM_PROMPT }],
      monitor(monitor) {
        monitor.addEventListener("downloadprogress", (event) => {
          download.hidden = false;
          download.value = event.loaded;
          setStatus(`Downloading the built-in model: ${Math.round(event.loaded * 100)}%`);
        });
      },
    });
    download.hidden = true;
    const tabs = await chrome.tabs.query({});
    const { entries, total } = tabEntries(tabs, Date.now(), chrome.runtime.getURL(""));
    if (entries.length === 0) {
      setStatus("No tabs to read.");
      return;
    }
    if (total > entries.length) {
      setStatus(`Reading the ${entries.length} oldest of ${total} tabs…`);
    } else {
      setStatus(`Reading ${entries.length} tabs…`);
    }
    const started = performance.now();
    const answer = await session.prompt(userPrompt(entries), {
      responseConstraint: RESPONSE_SCHEMA,
    });
    insights = parseInsights(answer, entries);
    render();
    const seconds = ((performance.now() - started) / 1000).toFixed(1);
    setStatus(`Read ${entries.length} tabs on this device in ${seconds} s.`);
  } catch (error) {
    setStatus(errorText(error), true);
  } finally {
    if (session) {
      session.destroy();
    }
    download.hidden = true;
    await refreshButton(false);
  }
}

async function closeChecked() {
  const wanted = new Set(checkedIds());
  closeButton.disabled = true;
  try {
    const open = await chrome.tabs.query({});
    const ids = open.map((tab) => tab.id).filter((id) => wanted.has(id));
    if (ids.length > 0) {
      await chrome.tabs.remove(ids);
    }
    const gone = new Set(wanted);
    insights = {
      close: insights.close.filter((pick) => !gone.has(pick.entry.id)),
      topics: insights.topics
        .map((topic) => ({ ...topic, tabs: topic.tabs.filter((entry) => !gone.has(entry.id)) }))
        .filter((topic) => topic.tabs.length > 0),
    };
    render();
    setStatus(ids.length === 1 ? "Closed 1 tab." : `Closed ${ids.length} tabs.`);
  } catch (error) {
    setStatus(errorText(error), true);
    updateCloseButton();
  }
}

analyzeButton.addEventListener("click", analyze);
closeButton.addEventListener("click", closeChecked);
refreshButton(true);
