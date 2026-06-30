const EXAMPLES = {
  commits: `SELECT
  substr(hash, 1, 10) AS commit,
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
  substr(cf.commit_hash, 1, 10) AS commit,
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
  substr(commit_hash, 1, 10) AS commit,
  content
FROM blame
WHERE path = 'src.txt'
ORDER BY line_no;`,
  planner: `EXPLAIN QUERY PLAN
SELECT hash, author_name
FROM commits
WHERE hash = (
  SELECT commit_hash
  FROM commit_files
  WHERE path = 'notes.txt'
  LIMIT 1
);`,
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
    this.pending.delete(message.id);
    if (message.type === "error") {
      request.reject(new Error(message.error || "Query failed"));
    } else {
      request.resolve(message.result);
    }
  }

  failAll(error) {
    this.rejectReady(error);
    for (const request of this.pending.values()) request.reject(error);
    this.pending.clear();
  }

  async query(sql) {
    await this.ready;
    const id = String(++this.sequence);
    const promise = new Promise((resolve, reject) => {
      this.pending.set(id, { resolve, reject });
    });
    this.worker.postMessage(JSON.stringify({ type: "query", id, sql }));
    return promise;
  }
}

const elements = {
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
let busy = false;

function setBusy(value) {
  busy = value;
  elements.run.disabled = value;
  elements.examples.disabled = value;
  elements.run.lastChild.textContent = value ? " Running…" : " Run query";
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
  if (busy) return;
  setBusy(true);
  elements.error.hidden = true;
  elements.queryStatus.textContent = "Running in the worker…";
  try {
    renderResult(await client.query(elements.sql.value));
  } catch (error) {
    showError(error);
  } finally {
    setBusy(false);
  }
}

elements.examples.addEventListener("change", () => {
  elements.sql.value = EXAMPLES[elements.examples.value];
  elements.sql.focus();
});
elements.run.addEventListener("click", runQuery);
elements.sql.addEventListener("keydown", (event) => {
  if (event.key === "Enter" && (event.ctrlKey || event.metaKey)) {
    event.preventDefault();
    runQuery();
  }
});

client.ready.then(() => {
  elements.statusDot.classList.add("ready");
  elements.runtimeStatus.textContent = "Go/WASM + SQLite ready";
  elements.queryStatus.textContent = "Ready";
  setBusy(false);
  runQuery();
}).catch((error) => {
  elements.statusDot.classList.add("failed");
  elements.runtimeStatus.textContent = "Runtime failed";
  elements.run.disabled = true;
  showError(error);
});
