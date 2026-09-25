// Packfile explorer entry point.
//
// Flow: type a repo → fetch refs → pick refs → fetch the pack through the CORS
// proxy → parse and resolve objects (in a worker when available) → index them
// for filtering, profiling, reachability, and path search → persist the raw
// pack in IndexedDB. Shareable URLs use ?pack=<stored id> and #<object oid> so
// refresh restores the same pack and selection.

import * as pako from "../vendor/pako/pako.esm.mjs";
import { makePakoInflate } from "./inflate.js";
import { parsePack, resolveObjects } from "./pack.js";
import { subtleComputeOid, subtleSha1Hex } from "./oid.js";
import { computeStats, queryObjects } from "./packIndex.js";
import { indexByOffset } from "./deltaChain.js";
import { computeReachability, defaultRoots } from "./reachability.js";
import { rootTreeOf, searchPaths, walkTree } from "./treeWalk.js";
import { verifyPackTrailer } from "./packTrailer.js";
import { diffPacks } from "./diffPacks.js";
import { looseObjectBytes } from "./looseObject.js";
import { normalizeRepoUrl, DEFAULT_PROXY } from "./proxy.js";
import { fetchPack, fetchRefs } from "./transport.js";
import { deleteRepo, listRepos, loadRepo, saveRepo } from "./store.js";
import { readUrlState, packShareUrl, writeUrlState } from "./urlState.js";
import {
  renderCompare,
  renderDetail,
  renderInsights,
  renderObjectList,
  renderPaths,
  renderRefPicker,
  renderRefs,
  renderSaved,
  renderStats,
  setStatus,
} from "./ui/render.js";

const inflate = makePakoInflate(pako);
const computeOid = subtleComputeOid(crypto.subtle);
const sha1Hex = subtleSha1Hex(crypto.subtle);

const els = {
  form: document.getElementById("fetch-form"),
  repo: document.getElementById("repo"),
  deepen: document.getElementById("deepen"),
  fetchBtn: document.getElementById("fetch-btn"),
  status: document.getElementById("status"),
  progress: document.getElementById("progress"),
  progressLog: document.getElementById("progress-log"),
  progressHide: document.getElementById("progress-hide"),
  refpicker: document.getElementById("refpicker"),
  refpickerList: document.getElementById("refpicker-list"),
  pickerDepth: document.getElementById("picker-depth"),
  pickerAll: document.getElementById("picker-all"),
  pickerNone: document.getElementById("picker-none"),
  pickerFetch: document.getElementById("picker-fetch"),
  saved: document.getElementById("saved"),
  savedList: document.getElementById("saved-list"),
  workspace: document.getElementById("workspace"),
  stats: document.getElementById("stats"),
  objectList: document.getElementById("object-list"),
  detail: document.getElementById("detail"),
  tabs: document.getElementById("tabs"),
  insights: document.getElementById("insights"),
  refsList: document.getElementById("refs-list"),
  pathSearch: document.getElementById("path-search"),
  pathsList: document.getElementById("paths-list"),
  filterType: document.getElementById("filter-type"),
  filterDelta: document.getElementById("filter-delta"),
  filterSort: document.getElementById("filter-sort"),
  filterReach: document.getElementById("filter-reach"),
  filterSearch: document.getElementById("filter-search"),
  navBack: document.getElementById("nav-back"),
  navFwd: document.getElementById("nav-fwd"),
  jumpForm: document.getElementById("jump-form"),
  jumpOid: document.getElementById("jump-oid"),
  copyLink: document.getElementById("copy-link"),
};

let session = null;
let currentTab = "objects";
const insightsState = { metric: "packed" };
let pendingRefs = null; // { base, refs, head } awaiting a ref-pick fetch

// In-app navigation history of selected oids.
let hist = [];
let histPos = -1;

// --- Off-thread parsing with a graceful fallback -------------------------

let worker = null;
let workerBroken = false;
let nextJobId = 1;
const pendingJobs = new Map();

function getWorker() {
  if (workerBroken) return null;
  if (worker) return worker;
  try {
    worker = new Worker(new URL("./parseWorker.js", import.meta.url), { type: "module" });
    worker.onmessage = (event) => {
      const data = event.data;
      const job = pendingJobs.get(data.id);
      if (!job) return;
      if (data.phase) {
        job.onPhase?.(data);
        return;
      }
      pendingJobs.delete(data.id);
      if (data.ok) job.resolve(data);
      else job.reject(new Error(data.error));
    };
    worker.onerror = () => {
      workerBroken = true;
      for (const job of pendingJobs.values()) job.reject(new Error("parse worker failed"));
      pendingJobs.clear();
      worker = null;
    };
  } catch {
    workerBroken = true;
    return null;
  }
  return worker;
}

async function parseAndResolve(pack, onPhase) {
  const w = getWorker();
  if (w) {
    try {
      const id = nextJobId++;
      const data = await new Promise((resolve, reject) => {
        pendingJobs.set(id, { resolve, reject, onPhase });
        w.postMessage({ pack, id });
      });
      return {
        parsed: data.parsed,
        resolved: {
          objects: data.resolved.objects,
          byOid: new Map(data.resolved.byOid),
          contentByOid: new Map(data.resolved.contentByOid),
          unresolved: data.resolved.unresolved,
        },
      };
    } catch {
      workerBroken = true; // fall through to main-thread parse
    }
  }
  const parsed = parsePack(pack, inflate);
  const resolved = await resolveObjects(parsed, computeOid);
  return { parsed, resolved };
}

// --- Fetch: refs then a ref-picked pack ----------------------------------

els.form.addEventListener("submit", async (event) => {
  event.preventDefault();
  let base;
  try {
    base = normalizeRepoUrl(els.repo.value);
  } catch (err) {
    setStatus(els.status, err.message, { error: true });
    return;
  }
  els.fetchBtn.disabled = true;
  try {
    setStatus(els.status, `Fetching refs for ${base}…`);
    const refs = await fetchRefs(DEFAULT_PROXY, base);
    pendingRefs = { base, refs: refs.refs, head: refs.head };
    els.pickerDepth.value = els.deepen.value || "1";
    renderRefPicker(els.refpickerList, refs.refs, refs.head);
    els.refpicker.hidden = false;
    els.saved.hidden = true;
    const branchCount = refs.refs.filter((r) => r.name !== "HEAD").length;
    setStatus(els.status, `${branchCount} refs. Pick what to fetch, then Fetch selected.`);
  } catch (err) {
    console.error(err);
    setStatus(els.status, err.message || String(err), { error: true });
  } finally {
    els.fetchBtn.disabled = false;
  }
});

els.pickerAll.addEventListener("click", () => setAllPicks(true));
els.pickerNone.addEventListener("click", () => setAllPicks(false));
function setAllPicks(checked) {
  els.refpickerList.querySelectorAll('input[type="checkbox"]').forEach((cb) => {
    cb.checked = checked;
  });
}

els.pickerFetch.addEventListener("click", async () => {
  if (!pendingRefs) return;
  const wants = [...els.refpickerList.querySelectorAll('input[type="checkbox"]:checked')].map(
    (cb) => cb.value,
  );
  if (wants.length === 0) {
    setStatus(els.status, "Select at least one ref to fetch.", { error: true });
    return;
  }
  const uniqueWants = [...new Set(wants)];
  const deepen = Math.max(1, Math.min(50, Number(els.pickerDepth.value) || 1));
  els.pickerFetch.disabled = true;
  resetProgress();
  try {
    setStatus(
      els.status,
      `Fetching pack (depth ${deepen}, ${uniqueWants.length} want${uniqueWants.length === 1 ? "" : "s"})…`,
    );
    const { pack, progress } = await fetchPack(DEFAULT_PROXY, pendingRefs.base, {
      wants: uniqueWants,
      deepen,
      onProgress: appendProgress,
    });
    const record = {
      base: pendingRefs.base,
      refs: pendingRefs.refs,
      head: pendingRefs.head,
      wants: uniqueWants,
      pack,
      progress,
    };
    els.refpicker.hidden = true;
    await openPack(record);
    await saveRepo(record);
    await refreshSavedQuiet();
    setStatus(els.status, `Loaded ${session.objects.length} objects from ${pendingRefs.base}`);
  } catch (err) {
    console.error(err);
    setStatus(els.status, err.message || String(err), { error: true });
  } finally {
    els.pickerFetch.disabled = false;
  }
});

document.getElementById("pack-file").addEventListener("change", async (event) => {
  const file = event.target.files && event.target.files[0];
  event.target.value = "";
  if (!file) return;
  try {
    setStatus(els.status, `Reading ${file.name}…`);
    const pack = new Uint8Array(await file.arrayBuffer());
    const record = { base: `file://${file.name}`, refs: [], head: null, wants: [], pack, progress: "" };
    els.refpicker.hidden = true;
    await openPack(record);
    await saveRepo(record);
    await refreshSavedQuiet();
    setStatus(els.status, `Loaded ${session.objects.length} objects from ${file.name}`);
  } catch (err) {
    console.error(err);
    setStatus(els.status, err.message || String(err), { error: true });
  }
});

// --- Progress log --------------------------------------------------------

function resetProgress() {
  els.progressLog.textContent = "";
  els.progress.hidden = false;
}
function appendProgress(text) {
  els.progress.hidden = false;
  els.progressLog.textContent += text;
  els.progressLog.scrollTop = els.progressLog.scrollHeight;
}
els.progressHide.addEventListener("click", () => {
  els.progress.hidden = true;
});

// --- Open and render a pack ---------------------------------------------

async function openPack(record, { objectId = null } = {}) {
  setStatus(els.status, `Parsing ${record.pack.length.toLocaleString()} pack bytes…`);
  const { parsed, resolved } = await parseAndResolve(record.pack, (p) =>
    setStatus(els.status, `Resolving ${p.count.toLocaleString()} objects…`),
  );
  const stats = computeStats(resolved.objects);
  const byOffset = indexByOffset(resolved.objects);

  const roots = defaultRoots({ head: record.head, refs: record.refs });
  const reachable =
    roots.length > 0
      ? computeReachability({ byOid: resolved.byOid, contentByOid: resolved.contentByOid, roots }).reachable
      : null;

  session = {
    packId: record.base,
    base: record.base,
    refs: record.refs || [],
    head: record.head,
    packBytes: record.pack,
    parsed,
    objects: resolved.objects,
    byOid: resolved.byOid,
    contentByOid: resolved.contentByOid,
    unresolved: resolved.unresolved,
    byOffset,
    stats,
    reachable,
    trailer: null,
    pathEntries: null,
    selectedOid: null,
  };

  els.saved.hidden = true;
  els.workspace.hidden = false;
  renderStats(els.stats, stats, { base: record.base });

  verifyPackTrailer(record.pack, parsed, sha1Hex)
    .then((trailer) => {
      if (session && session.packId === record.base) {
        session.trailer = trailer;
        if (currentTab === "insights") renderActiveTab();
      }
    })
    .catch(() => {});

  hist = [];
  histPos = -1;

  let initial = null;
  if (objectId && resolved.byOid.has(objectId)) initial = resolved.byOid.get(objectId);
  else if (record.head && resolved.byOid.has(record.head)) initial = resolved.byOid.get(record.head);
  else initial = resolved.objects.find((o) => o.typeName === "commit") || resolved.objects[0];

  if (initial && initial.oid) go(initial.oid);
  else showObject(initial || null, { push: false });
  refreshList();
  renderActiveTab();
}

// --- Object list ---------------------------------------------------------

function refreshList() {
  if (!session) return;
  const rows = queryObjects(session.objects, {
    type: els.filterType.value || null,
    deltaType: els.filterDelta.value || null,
    search: els.filterSearch.value,
    sort: els.filterSort.value,
    reachability: els.filterReach.value || null,
    reachable: session.reachable,
  });
  renderObjectList(els.objectList, rows, session.selectedOid, (obj) => {
    if (obj.oid) go(obj.oid);
    else showObject(obj, { push: false });
  });
}

for (const el of [els.filterType, els.filterDelta, els.filterSort, els.filterReach, els.filterSearch]) {
  el.addEventListener("input", () => refreshList());
}

// --- Navigation (in-app history + URL) ----------------------------------

function go(oid) {
  if (!session) return;
  const obj = session.byOid.get(oid);
  if (!obj) {
    setStatus(els.status, `Object ${oid.slice(0, 8)} is not in this pack.`, { error: true });
    return;
  }
  if (hist[histPos] !== oid) {
    hist = hist.slice(0, histPos + 1);
    hist.push(oid);
    histPos = hist.length - 1;
  }
  showObject(obj, { push: false });
  updateNavButtons();
}

function showObject(obj, { push = true } = {}) {
  if (!session) return;
  if (push && obj && obj.oid) {
    go(obj.oid);
    return;
  }
  session.selectedOid = obj?.oid || null;
  renderDetail(els.detail, obj, session, { onSelectOid: go, onDownload: downloadObject });
  refreshList();
  writeUrlState({ packId: session.packId, objectId: session.selectedOid });
}

function updateNavButtons() {
  els.navBack.disabled = histPos <= 0;
  els.navFwd.disabled = histPos >= hist.length - 1;
}

els.navBack.addEventListener("click", () => {
  if (histPos > 0) {
    histPos -= 1;
    showObject(session.byOid.get(hist[histPos]), { push: false });
    updateNavButtons();
  }
});
els.navFwd.addEventListener("click", () => {
  if (histPos < hist.length - 1) {
    histPos += 1;
    showObject(session.byOid.get(hist[histPos]), { push: false });
    updateNavButtons();
  }
});

els.jumpForm.addEventListener("submit", (event) => {
  event.preventDefault();
  const oid = els.jumpOid.value.trim().toLowerCase();
  if (!/^[0-9a-f]{40}$/.test(oid)) {
    setStatus(els.status, "Enter a full 40-character oid.", { error: true });
    return;
  }
  go(oid);
  els.jumpOid.value = "";
});

els.copyLink.addEventListener("click", async () => {
  if (!session) return;
  const url = packShareUrl(session.packId, session.selectedOid);
  try {
    await navigator.clipboard.writeText(url);
    setStatus(els.status, "Link copied to clipboard.");
  } catch {
    setStatus(els.status, url);
  }
});

// --- Download a loose object --------------------------------------------

function downloadObject(oid) {
  if (!session) return;
  const obj = session.byOid.get(oid);
  const content = session.contentByOid.get(oid);
  if (!obj || !content) return;
  const bytes = looseObjectBytes(obj.typeName, content, (b) => pako.deflate(b));
  const blob = new Blob([bytes], { type: "application/octet-stream" });
  const url = URL.createObjectURL(blob);
  const a = document.createElement("a");
  a.href = url;
  a.download = oid;
  document.body.appendChild(a);
  a.click();
  a.remove();
  URL.revokeObjectURL(url);
}

// --- Tabs ----------------------------------------------------------------

els.tabs.addEventListener("click", (event) => {
  const btn = event.target.closest(".tab");
  if (!btn) return;
  setTab(btn.dataset.tab);
});

function setTab(tab) {
  currentTab = tab;
  els.tabs.querySelectorAll(".tab").forEach((b) => {
    b.setAttribute("aria-selected", String(b.dataset.tab === tab));
  });
  document.querySelectorAll(".tab-panel").forEach((p) => {
    p.hidden = p.dataset.panel !== tab;
  });
  renderActiveTab();
}

function renderActiveTab() {
  if (!session) return;
  if (currentTab === "insights") {
    renderInsights(els.insights, session, { ...insightsState, savedCount: savedCount }, {
      onSelectOid: go,
      onMetricChange: (metric) => {
        insightsState.metric = metric;
        renderActiveTab();
      },
      onFilterUnreachable: () => {
        setTab("objects");
        els.filterReach.value = "unreachable";
        refreshList();
      },
      onCompare: startCompare,
    });
  } else if (currentTab === "refs") {
    renderRefs(els.refsList, session, go);
  } else if (currentTab === "paths") {
    ensurePathEntries();
    renderPaths(els.pathsList, searchPaths(session.pathEntries || [], els.pathSearch.value), go);
  }
}

els.pathSearch.addEventListener("input", () => {
  if (!session) return;
  ensurePathEntries();
  renderPaths(els.pathsList, searchPaths(session.pathEntries || [], els.pathSearch.value), go);
});

function ensurePathEntries() {
  if (!session || session.pathEntries) return;
  let treeSource = null;
  if (session.head && session.byOid.has(session.head)) treeSource = session.head;
  else if (session.selectedOid) treeSource = session.selectedOid;
  else {
    const commit = session.objects.find((o) => o.typeName === "commit");
    treeSource = commit ? commit.oid : null;
  }
  const treeOid = treeSource ? rootTreeOf(treeSource, session.byOid, session.contentByOid) : null;
  session.pathEntries = treeOid ? walkTree(treeOid, session.byOid, session.contentByOid) : [];
}

// --- Compare -------------------------------------------------------------

async function startCompare() {
  const rows = await listRepos();
  const others = rows.filter((r) => r.key !== session.packId);
  if (others.length === 0) {
    setStatus(els.status, "No other saved packs to compare against.", { error: true });
    return;
  }
  const parts = [`<h2>Compare with…</h2><ul class="compare-choices">`];
  for (const row of others) {
    parts.push(
      `<li><button type="button" class="quiet" data-compare="${escapeAttr(row.key)}">` +
        `${escapeAttr(row.base)}</button></li>`,
    );
  }
  parts.push(`</ul>`);
  els.detail.innerHTML = parts.join("");
  els.detail.querySelectorAll("[data-compare]").forEach((btn) => {
    btn.addEventListener("click", () => compareWith(btn.getAttribute("data-compare")));
  });
}

async function compareWith(key) {
  try {
    setStatus(els.status, "Loading pack to compare…");
    const record = await loadRepo(key);
    if (!record) throw new Error("saved pack not found");
    const { resolved } = await parseAndResolve(record.pack);
    const diff = diffPacks(session.objects, resolved.objects);
    renderCompare(els.detail, diff, { aName: session.base, bName: record.base }, (oid) => {
      if (session.byOid.has(oid)) go(oid);
      else setStatus(els.status, `${oid.slice(0, 8)} is only in the other pack.`);
    });
    setStatus(els.status, `Compared with ${record.base}`);
  } catch (err) {
    setStatus(els.status, err.message || String(err), { error: true });
  }
}

function escapeAttr(value) {
  return String(value).replace(/&/g, "&amp;").replace(/"/g, "&quot;").replace(/</g, "&lt;");
}

// --- Saved packs ---------------------------------------------------------

let savedCount = 0;

async function refreshSaved() {
  const rows = await listRepos();
  savedCount = rows.length;
  if (rows.length === 0 || session) {
    els.saved.hidden = true;
    return;
  }
  els.saved.hidden = false;
  renderSaved(els.savedList, rows, {
    onOpen: async (key) => {
      try {
        setStatus(els.status, "Loading saved pack…");
        await openSavedPack(key);
        setStatus(els.status, `Opened saved pack for ${session.base}`);
        await refreshSavedQuiet();
      } catch (err) {
        setStatus(els.status, err.message, { error: true });
      }
    },
    onDelete: async (key) => {
      await deleteRepo(key);
      const { packId } = readUrlState();
      if (packId === key) writeUrlState({ packId: null, objectId: null });
      if (session?.packId === key) {
        session = null;
        els.workspace.hidden = true;
        renderDetail(els.detail, null, session, {});
      }
      await refreshSaved();
    },
  });
}

// Refresh the saved-count without unhiding the list while a pack is open.
async function refreshSavedQuiet() {
  const rows = await listRepos();
  savedCount = rows.length;
}

async function openSavedPack(packId, { objectId = null } = {}) {
  const record = await loadRepo(packId);
  if (!record) throw new Error(`No saved pack "${packId}" in this browser`);
  els.repo.value = record.base;
  await openPack(record, { objectId });
}

// --- URL restore ---------------------------------------------------------

async function restoreFromUrl() {
  const { packId, objectId } = readUrlState();
  if (!packId) return;
  if (session?.packId === packId) {
    if (objectId && session.byOid.has(objectId)) go(objectId);
    return;
  }
  try {
    setStatus(els.status, "Restoring pack from link…");
    await openSavedPack(packId, { objectId });
    setStatus(els.status, `Restored ${session.objects.length} objects from ${session.base}`);
    await refreshSavedQuiet();
  } catch (err) {
    console.error(err);
    setStatus(els.status, err.message || String(err), { error: true });
    await refreshSaved();
  }
}

window.addEventListener("hashchange", () => {
  const { objectId } = readUrlState();
  if (objectId && session?.byOid.has(objectId) && objectId !== session.selectedOid) go(objectId);
});

window.addEventListener("popstate", () => {
  void restoreFromUrl();
});

async function boot() {
  const { packId } = readUrlState();
  if (packId) await restoreFromUrl();
  else await refreshSaved();
}

boot().catch((err) => console.error(err));
