import { REGIONS } from "./regions.js";
import { pingRegion } from "./ping.js";
import { compareResults, fastestId, median } from "./stats.js";

const INITIAL_ROUNDS = 10;

const tbody = document.querySelector("#results tbody");
const statusEl = document.querySelector("#status");
const stopStart = document.querySelector("#stopstart");
const howButton = document.querySelector("#how");
const howDialog = document.querySelector("#how-dialog");
const timingNote = document.querySelector("#timing-note");
const headerButtons = document.querySelectorAll("th[data-sort] button");

const state = {
  running: false,
  warming: false,
  round: 0,
  targetRounds: INITIAL_ROUNDS,
  sortKey: "median",
  sortDir: "ascending",
  controller: null,
  sawBreakdown: false,
  rows: REGIONS.map((region) => ({
    id: region.id,
    location: region.location,
    samples: [],
    median: null,
    lastBreakdown: null,
  })),
};

function nonce() {
  return `${Date.now()}-${Math.random().toString(16).slice(2)}`;
}

function getEntry(url) {
  const entries = performance.getEntriesByName(url);
  if (entries.length === 0) {
    return null;
  }
  return entries[entries.length - 1];
}

function formatMs(value) {
  return `${Math.round(value)} ms`;
}

function sortedRows() {
  const copy = state.rows.slice();
  copy.sort((a, b) =>
    compareResults(a, b, state.sortKey, state.sortDir),
  );
  return copy;
}

function render() {
  const fastest = fastestId(state.rows);
  const rows = sortedRows();
  tbody.replaceChildren();
  for (const row of rows) {
    const tr = document.createElement("tr");
    if (row.id === fastest) {
      tr.className = "fastest-region";
    }
    const loc = document.createElement("th");
    loc.scope = "row";
    loc.textContent = row.location;
    const region = document.createElement("td");
    region.className = "region-id";
    region.textContent = row.id;
    const latency = document.createElement("td");
    latency.className = "num";
    if (row.median === null) {
      latency.textContent = "—";
    } else {
      latency.textContent = formatMs(row.median);
      latency.title = `${row.samples.length} samples`;
    }
    tr.append(loc, region, latency);
    tbody.append(tr);
  }

  for (const button of headerButtons) {
    const th = button.parentElement;
    const key = th.dataset.sort;
    if (key === state.sortKey) {
      th.setAttribute("aria-sort", state.sortDir);
    } else {
      th.setAttribute("aria-sort", "none");
    }
  }

  stopStart.classList.toggle("running", state.running);
  const stoppedLabel = stopStart.querySelector("[data-when='stopped']");
  const runningLabel = stopStart.querySelector("[data-when='running']");
  stoppedLabel.hidden = state.running;
  runningLabel.hidden = !state.running;
  stopStart.setAttribute("aria-pressed", String(state.running));

  if (state.running) {
    if (state.warming || state.round === 0) {
      statusEl.textContent = "Pinging";
    } else {
      statusEl.textContent = `Pinging · round ${state.round} of ${state.targetRounds}`;
    }
  } else if (state.round === 0) {
    statusEl.textContent = "Waiting to ping";
  } else {
    statusEl.textContent = `Stopped · ${state.round} rounds`;
  }

  timingNote.hidden = !state.sawBreakdown;
}

async function pingOne(row, signal, record) {
  const result = await pingRegion(row.id, {
    nonce: nonce(),
    fetchImpl: fetch.bind(globalThis),
    now: () => performance.now(),
    getEntry,
    signal,
  });
  if (result.aborted || !result.ok || result.duration === null) {
    return;
  }
  if (!record) {
    return;
  }
  row.samples.push(result.duration);
  row.median = median(row.samples);
  if (result.breakdown) {
    row.lastBreakdown = result.breakdown;
    state.sawBreakdown = true;
  }
  render();
}

async function pingRound(signal, record) {
  if (record) {
    state.round += 1;
    render();
  }
  const work = state.rows.map((row) => pingOne(row, signal, record));
  await Promise.all(work);
}

async function runRounds(count) {
  if (state.running) {
    return;
  }
  state.running = true;
  state.warming = true;
  state.targetRounds = state.round + count;
  state.controller = new AbortController();
  const signal = state.controller.signal;
  render();
  try {
    if (!signal.aborted) {
      await pingRound(signal, false);
    }
    state.warming = false;
    for (let i = 0; i < count; i += 1) {
      if (signal.aborted) {
        break;
      }
      await pingRound(signal, true);
    }
  } finally {
    state.running = false;
    state.warming = false;
    state.controller = null;
    render();
  }
}

function stop() {
  if (state.controller) {
    state.controller.abort();
  }
}

stopStart.addEventListener("click", () => {
  if (state.running) {
    stop();
  } else {
    runRounds(1);
  }
});

howButton.addEventListener("click", () => {
  howDialog.showModal();
});

for (const button of headerButtons) {
  button.addEventListener("click", () => {
    const key = button.parentElement.dataset.sort;
    if (state.sortKey === key) {
      if (state.sortDir === "ascending") {
        state.sortDir = "descending";
      } else {
        state.sortDir = "ascending";
      }
    } else {
      state.sortKey = key;
      state.sortDir = "ascending";
    }
    render();
  });
}

if (typeof performance.setResourceTimingBufferSize === "function") {
  performance.setResourceTimingBufferSize(2000);
}

runRounds(INITIAL_ROUNDS);
