const probeURL = new URL("./probe.json", import.meta.url).href.replaceAll("'", "''");

const EXAMPLES = {
  commits: `SELECT
  substr(hash, 1, 10) AS commit_id,
  author_name,
  summary,
  author_when
FROM commits
ORDER BY author_when DESC;`,
  authors: `SELECT
  c.author_name,
  count(DISTINCT c.hash) AS commits,
  sum(cf.additions) AS lines_added,
  sum(cf.deletions) AS lines_deleted
FROM commits AS c
JOIN commit_files AS cf ON cf.commit_hash = c.hash
GROUP BY c.author_name
ORDER BY lines_added DESC;`,
  files: `SELECT
  path,
  type,
  size,
  lines,
  is_binary
FROM files
ORDER BY path;`,
  changes: `SELECT
  substr(cf.commit_hash, 1, 10) AS commit_id,
  c.author_name,
  cf.change,
  cf.path,
  cf.additions,
  cf.deletions
FROM commit_files AS cf
JOIN commits AS c ON c.hash = cf.commit_hash
ORDER BY c.author_when DESC, cf.path;`,
  blame: `SELECT
  line_no,
  author_name,
  substr(commit_hash, 1, 10) AS commit_id,
  content
FROM blame
WHERE path = 'README.md'
ORDER BY line_no;`,
  planner: `EXPLAIN QUERY PLAN
SELECT hash, author_name
FROM commits
WHERE hash = (
  SELECT commit_hash
  FROM commit_files
  WHERE path = 'README.md'
  LIMIT 1
);`,
  network: `SELECT
  http_status,
  body
FROM network_probe
WHERE url = '${probeURL}';`,
};

class GitDBWorker {
  constructor() {
    this.worker = new Worker(new URL("./worker.js", import.meta.url));
    this.pending = new Map();
    this.sequence = 0;
    this.ready = new Promise((resolve, reject) => {
      this.resolveReady = resolve;
      this.rejectReady = reject;
    });
    this.worker.addEventListener("message", (event) => this.onMessage(event));
    this.worker.addEventListener("error", (event) => {
      this.failAll(new Error(event.message || "Web Worker failed"));
    });
  }

  onMessage(event) {
    let message;
    try {
      message = JSON.parse(event.data);
    } catch {
      this.failAll(new Error("Worker returned an invalid response"));
      return;
    }

    if (message.type === "ready") {
      this.resolveReady();
      return;
    }
    if (message.type === "fatal") {
      this.failAll(new Error(message.error || "Worker initialization failed"));
      return;
    }

    const request = this.pending.get(message.id);
    if (!request) return;
    if (message.type === "progress") {
      request.onProgress?.(message.message || "Working…");
      return;
    }
    this.pending.delete(message.id);
    if (message.type === "error") {
      request.reject(new Error(message.error || "Query failed"));
    } else {
      request.resolve(message.type === "loaded" ? message.repository : message.result);
    }
  }

  failAll(error) {
    this.rejectReady(error);
    for (const request of this.pending.values()) request.reject(error);
    this.pending.clear();
  }

  async query(sql) {
    return this.send("query", { sql });
  }

  async clone(options, onProgress) {
    return this.send("clone", options, onProgress);
  }

  async send(type, payload, onProgress) {
    await this.ready;
    const id = String(++this.sequence);
    const promise = new Promise((resolve, reject) => {
      this.pending.set(id, { resolve, reject, onProgress });
    });
    this.worker.postMessage(JSON.stringify({ type, id, ...payload }));
    return promise;
  }
}

const elements = {
  repositoryForm: document.querySelector("#repository-form"),
  repositoryURL: document.querySelector("#repository-url"),
  proxy: document.querySelector("#cors-proxy"),
  depth: document.querySelector("#clone-depth"),
  singleBranch: document.querySelector("#single-branch"),
  load: document.querySelector("#load-repository"),
  cloneStatus: document.querySelector("#clone-status"),
  repositoryLabel: document.querySelector("#repository-label"),
  run: document.querySelector("#run-query"),
  sql: document.querySelector("#sql-input"),
  examples: document.querySelector("#example-select"),
  runtimeStatus: document.querySelector("#runtime-status"),
  statusDot: document.querySelector("#status-dot"),
  queryStatus: document.querySelector("#query-status"),
  error: document.querySelector("#error-panel"),
  result: document.querySelector("#result-panel"),
  summary: document.querySelector("#result-summary"),
  timing: document.querySelector("#result-timing"),
  table: document.querySelector("#result-table"),
};

const client = new GitDBWorker();
let runtimeReady = false;
let repositoryLoaded = false;
let cloneBusy = false;
let queryBusy = false;

function syncControls() {
  elements.load.disabled = !runtimeReady || cloneBusy || queryBusy;
  elements.run.disabled = !repositoryLoaded || cloneBusy || queryBusy;
  elements.examples.disabled = !repositoryLoaded || cloneBusy || queryBusy;
  elements.sql.disabled = !repositoryLoaded || cloneBusy;
  elements.load.textContent = cloneBusy ? "Cloning…" : "Clone & open";
  elements.run.lastChild.textContent = queryBusy ? " Running…" : " Run query";
}

function showError(error) {
  elements.result.hidden = true;
  elements.error.hidden = false;
  elements.error.textContent = error.message || String(error);
  elements.queryStatus.textContent = "Query failed";
}

function renderResult(result) {
  elements.error.hidden = true;
  elements.result.hidden = false;
  elements.table.replaceChildren();

  const head = document.createElement("thead");
  const headRow = document.createElement("tr");
  for (const column of result.columns) {
    const th = document.createElement("th");
    th.scope = "col";
    th.textContent = column;
    headRow.append(th);
  }
  head.append(headRow);

  const body = document.createElement("tbody");
  for (const row of result.rows) {
    const tr = document.createElement("tr");
    for (const value of row) {
      const td = document.createElement("td");
      if (value === null) {
        td.className = "null";
        td.textContent = "NULL";
      } else {
        td.textContent = String(value);
        td.title = String(value);
      }
      tr.append(td);
    }
    body.append(tr);
  }
  elements.table.append(head, body);

  const suffix = result.truncated ? " (limited to 500)" : "";
  elements.summary.textContent = `${result.rows.length} row${result.rows.length === 1 ? "" : "s"}${suffix}`;
  elements.timing.textContent = `${result.elapsedMs} ms in WebAssembly`;
  elements.queryStatus.textContent = "Query complete";
}

async function runQuery() {
  if (queryBusy || cloneBusy || !repositoryLoaded) return;
  queryBusy = true;
  syncControls();
  elements.error.hidden = true;
  elements.queryStatus.textContent = "Running in the worker…";
  try {
    renderResult(await client.query(elements.sql.value));
  } catch (error) {
    showError(error);
  } finally {
    queryBusy = false;
    syncControls();
  }
}

async function loadRepository(event) {
  event.preventDefault();
  if (cloneBusy || queryBusy || !runtimeReady) return;

  cloneBusy = true;
  syncControls();
  elements.error.hidden = true;
  elements.cloneStatus.textContent = "Starting clone…";
  try {
    const repository = await client.clone({
      url: elements.repositoryURL.value.trim(),
      proxy: elements.proxy.value.trim(),
      depth: Number.parseInt(elements.depth.value, 10) || 0,
      singleBranch: elements.singleBranch.checked,
    }, (message) => {
      elements.cloneStatus.textContent = message;
    });
    repositoryLoaded = true;
    const head = repository.head ? ` @ ${repository.head.slice(0, 10)}` : "";
    elements.repositoryLabel.textContent = `${repository.url}${head}`;
    elements.cloneStatus.textContent = "Repository loaded. SQL tables are ready.";
  } catch (error) {
    const proxyHint = elements.proxy.value.trim()
      ? " Check the repository URL and CORS proxy."
      : " Most Git hosts require a CORS proxy in the browser.";
    elements.cloneStatus.textContent = `${error.message}${proxyHint}`;
    return;
  } finally {
    cloneBusy = false;
    syncControls();
  }
  runQuery();
}

elements.examples.addEventListener("change", () => {
  elements.sql.value = EXAMPLES[elements.examples.value];
  elements.sql.focus();
});
elements.repositoryForm.addEventListener("submit", loadRepository);
elements.run.addEventListener("click", runQuery);
elements.sql.addEventListener("keydown", (event) => {
  if (event.key === "Enter" && (event.ctrlKey || event.metaKey)) {
    event.preventDefault();
    runQuery();
  }
});

client.ready.then(() => {
  runtimeReady = true;
  elements.statusDot.classList.add("ready");
  elements.runtimeStatus.textContent = "Go/WASM + SQLite ready";
  elements.cloneStatus.textContent = "Enter a repository and clone it into this tab.";
  elements.queryStatus.textContent = "Load a repository to begin";
  syncControls();
}).catch((error) => {
  elements.statusDot.classList.add("failed");
  elements.runtimeStatus.textContent = "Runtime failed";
  runtimeReady = false;
  syncControls();
  showError(error);
});
