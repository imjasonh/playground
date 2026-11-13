// Packfile explorer entry point.
//
// Flow: type a repo → fetch refs → pick refs → fetch the pack through the CORS
// proxy → parse and resolve objects (in a worker when available) → index them
// for filtering, profiling, reachability, and path search → persist the raw
// pack in IndexedDB. Shareable URLs use ?pack=<stored id> and #<object oid> so
// refresh restores the same pack and selection.

import * as pako from "../vendor/pako/pako.esm.mjs";
import { makePakoInflate, makePakoStreamInflate } from "./inflate.js";
import { parsePack, resolveObjects } from "./pack.js";
import { blobReader } from "./packReader.js";
import { indexPack, lazyContent } from "./packStream.js";
import { annotatePackEntrySlice } from "./packVisual.js";
import { formatBytes } from "./format.js";
import { subtleComputeOid, subtleSha1Hex } from "./oid.js";
import { computeStats, queryObjects } from "./packIndex.js";
import { indexByOffset } from "./deltaChain.js";
import { computeReachability, defaultRoots } from "./reachability.js";
import { attributeBlobs } from "./attribution.js";
import { pathIndex, rootTreeOf, searchPaths, walkTree } from "./treeWalk.js";
import { verifyPackTrailer } from "./packTrailer.js";
import { diffPacks } from "./diffPacks.js";
import { looseObjectBytes } from "./looseObject.js";
import { normalizeRepoUrl, DEFAULT_PROXY } from "./proxy.js";
import { fetchPack, fetchRefs } from "./transport.js";
import { deleteRepo, listRepos, loadRepo, saveRepo } from "./store.js";
import { readUrlState, packShareUrl, writeUrlState } from "./urlState.js";
import {
  markSelected,
  renderAuthorFilter,
  renderDetail,
  renderObjectRows,
  renderOverview,
  renderPackTitle,
  renderPaths,
  renderRefPicker,
  renderRefs,
  renderSaved,
  setStatus,
} from "./ui/render.js";

const inflate = makePakoInflate(pako);
const streamInflate = makePakoStreamInflate(pako);
const computeOid = subtleComputeOid(crypto.subtle);
const sha1Hex = subtleSha1Hex(crypto.subtle);

// Packs at or above this size are opened by streaming index rather than by
// reading the whole file into one ArrayBuffer (which browsers cap near 2 GiB).
const LARGE_PACK_BYTES = 256 * 1024 * 1024;
// Don't inflate a single object larger than this into memory for its detail
// view; show its metadata only. Keeps a huge blob from exhausting the tab.
const LARGE_CONTENT_CAP = 64 * 1024 * 1024;
// Rows rendered in the object list; filters narrow the rest.
const LIST_LIMIT = 500;

const $ = (id) => document.getElementById(id);
const els = {
  app: $("app"),
  form: $("fetch-form"),
  repo: $("repo"),
  deepen: $("deepen"),
  fetchBtn: $("fetch-btn"),
  packFile: $("pack-file"),
  status: $("status"),
  tray: $("tray"),
  progress: $("progress"),
  progressLog: $("progress-log"),
  progressHide: $("progress-hide"),
  refpicker: $("refpicker"),
  refpickerList: $("refpicker-list"),
  pickerDepth: $("picker-depth"),
  pickerAll: $("picker-all"),
  pickerNone: $("picker-none"),
  pickerFetch: $("picker-fetch"),
  landing: $("landing"),
  saved: $("saved"),
  savedList: $("saved-list"),
  workspace: $("workspace"),
  packTitle: $("pack-title"),
  objectList: $("object-list"),
  objectCount: $("object-count"),
  filterType: $("filter-type"),
  filterDelta: $("filter-delta"),
  filterSort: $("filter-sort"),
  filterReach: $("filter-reach"),
  filterAuthor: $("filter-author"),
  filterSearch: $("filter-search"),
  pathSearch: $("path-search"),
  pathsList: $("paths-list"),
  pathsCount: $("paths-count"),
  refsList: $("refs-list"),
  refsCount: $("refs-count"),
  overview: $("overview"),
  detail: $("detail"),
  navBack: $("nav-back"),
  navFwd: $("nav-fwd"),
  jumpForm: $("jump-form"),
  jumpOid: $("jump-oid"),
  copyLink: $("copy-link"),
};

let session = null;
let navTab = "objects";
let view = "overview";
const overviewState = { metric: "packed", authorMetric: "packed", compare: null };
let savedCount = 0;
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

function reportError(err) {
  console.error(err);
  setStatus(els.status, err.message || String(err), { error: true });
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
    updateTray();
    const branchCount = refs.refs.filter((r) => r.name !== "HEAD").length;
    setStatus(els.status, `${branchCount} ref${branchCount === 1 ? "" : "s"} in ${base}. HEAD is selected.`);
    els.pickerFetch.focus();
  } catch (err) {
    reportError(err);
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
    await openPack(record);
    els.refpicker.hidden = true;
    els.progress.hidden = true;
    updateTray();
    await saveRepo(record);
    await refreshSavedCount();
    setStatus(els.status, `Loaded ${session.objects.length.toLocaleString()} objects from ${record.base}.`);
  } catch (err) {
    reportError(err);
  } finally {
    els.pickerFetch.disabled = false;
  }
});

els.packFile.addEventListener("change", async (event) => {
  const file = event.target.files && event.target.files[0];
  event.target.value = "";
  if (!file) return;
  try {
    els.refpicker.hidden = true;
    updateTray();
    if (file.size >= LARGE_PACK_BYTES) {
      await openLargePack(file);
      setStatus(
        els.status,
        `Loaded ${session.objects.length.toLocaleString()} objects from ${file.name} ` +
          `(${formatBytes(file.size)}, streamed from disk, not saved).`,
      );
      return;
    }
    setStatus(els.status, `Reading ${file.name}…`);
    const pack = new Uint8Array(await file.arrayBuffer());
    const record = { base: `file://${file.name}`, refs: [], head: null, wants: [], pack, progress: "" };
    await openPack(record);
    await saveRepo(record);
    await refreshSavedCount();
    setStatus(els.status, `Loaded ${session.objects.length.toLocaleString()} objects from ${file.name}.`);
  } catch (err) {
    reportError(err);
  }
});

// --- Tray: ref picker and server progress --------------------------------

function updateTray() {
  els.tray.hidden = els.refpicker.hidden && els.progress.hidden;
}

function resetProgress() {
  els.progressLog.textContent = "";
  els.progress.hidden = false;
  updateTray();
}

function appendProgress(text) {
  els.progress.hidden = false;
  updateTray();
  els.progressLog.textContent += text;
  els.progressLog.scrollTop = els.progressLog.scrollHeight;
}

els.progressHide.addEventListener("click", () => {
  els.progress.hidden = true;
  updateTray();
});

// --- Open a pack ----------------------------------------------------------

async function openPack(record, { objectId = null } = {}) {
  setStatus(els.status, `Parsing ${formatBytes(record.pack.length)} of pack data…`);
  const { parsed, resolved } = await parseAndResolve(record.pack, (p) =>
    setStatus(els.status, `Resolving ${p.count.toLocaleString()} objects…`),
  );

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
    progress: record.progress || "",
    packBytes: record.pack,
    parsed,
    objects: resolved.objects,
    byOid: resolved.byOid,
    contentByOid: resolved.contentByOid,
    unresolved: resolved.unresolved,
    byOffset: indexByOffset(resolved.objects),
    stats: computeStats(resolved.objects),
    reachable,
    attribution: attributeBlobs(resolved),
    trailer: null,
    selectedOid: null,
  };
  indexPaths(session);

  const opened = session;
  verifyPackTrailer(record.pack, parsed, sha1Hex)
    .then((trailer) => {
      if (session === opened) {
        session.trailer = trailer;
        renderOverviewView();
      }
    })
    .catch(() => {});

  await showPack({ objectId });
}

// Run the streaming index in the worker, falling back to the main thread.
async function indexLargePack(file, onPhase) {
  const w = getWorker();
  if (w) {
    try {
      const id = nextJobId++;
      const data = await new Promise((resolve, reject) => {
        pendingJobs.set(id, { resolve, reject, onPhase });
        w.postMessage({ file, mode: "index", id });
      });
      return {
        version: data.index.version,
        count: data.index.count,
        objects: data.index.objects,
        contentByOid: new Map(data.index.contentByOid),
        unresolved: data.index.unresolved,
        trailer: data.index.trailer,
        trailerOffset: data.index.trailerOffset,
      };
    } catch {
      workerBroken = true; // fall through to a main-thread index
    }
  }
  return indexPack({
    reader: blobReader(file),
    inflate: streamInflate,
    computeOid,
    onProgress: onPhase ? (p) => onPhase({ phase: "index", ...p }) : null,
  });
}

async function openLargePack(file) {
  setStatus(els.status, `Indexing ${file.name} (${formatBytes(file.size)})…`);
  const index = await indexLargePack(file, (p) => {
    if (p.phase === "index" && p.count) {
      setStatus(
        els.status,
        `Indexing ${file.name}: ${p.done.toLocaleString()} of ${p.count.toLocaleString()} objects…`,
      );
    }
  });

  const byOid = new Map();
  for (const obj of index.objects) {
    if (obj.oid) byOid.set(obj.oid, obj);
  }

  session = {
    packId: `file://${file.name}`,
    base: `file://${file.name}`,
    refs: [],
    head: null,
    progress: "",
    packBytes: null,
    large: true,
    contentCap: LARGE_CONTENT_CAP,
    lazy: lazyContent({ reader: blobReader(file), inflate: streamInflate, objects: index.objects, byOid }),
    parsed: { version: index.version, count: index.count, trailer: index.trailer },
    objects: index.objects,
    byOid,
    contentByOid: index.contentByOid,
    unresolved: index.unresolved,
    byOffset: indexByOffset(index.objects),
    stats: computeStats(index.objects),
    reachable: null,
    attribution: attributeBlobs({ objects: index.objects, byOid, contentByOid: index.contentByOid }),
    trailer: null,
    selectedOid: null,
    view: null,
  };
  indexPaths(session);
  await showPack({});
}

// Name objects by their path in the HEAD tree (or the first commit's tree).
function indexPaths(s) {
  let source = s.head && s.byOid.has(s.head) ? s.head : null;
  if (!source) source = s.objects.find((o) => o.typeName === "commit")?.oid || null;
  s.pathRoot = source ? rootTreeOf(source, s.byOid, s.contentByOid) : null;
  s.pathByOid = pathIndex(s.pathRoot, s.contentByOid);
  s.pathEntries = null;
}

// Render a freshly opened session: navigator, overview, and the requested
// object (or the overview when none was requested).
async function showPack({ objectId = null }) {
  hist = [];
  histPos = -1;
  updateNavButtons();
  overviewState.compare = null;
  for (const el of [els.filterType, els.filterDelta, els.filterReach, els.filterSearch]) el.value = "";
  els.filterSort.value = "offset";
  els.pathSearch.value = "";
  els.filterReach.disabled = !session.reachable;
  renderAuthorFilter(els.filterAuthor, session.attribution);

  els.landing.hidden = true;
  els.workspace.hidden = false;
  renderPackTitle(els.packTitle, session);
  refreshList();
  renderNavPanel();
  renderOverviewView();

  if (objectId && session.byOid.has(objectId)) {
    await go(objectId);
  } else {
    renderDetail(els.detail, null, session);
    setView("overview");
    writeUrlState({ packId: session.packId, objectId: null });
  }
}

function closePack() {
  session = null;
  els.workspace.hidden = true;
  els.landing.hidden = false;
}

// Resolve, from the File, everything the detail pane needs for `obj`: its own
// content, its delta base content, and the annotated raw entry bytes.
async function prefetchView(obj) {
  const content = new Map();
  const raw = await session.lazy.rawEntry(obj.index);

  const target = session.objects[obj.index];
  if (obj.oid && target && target.declaredSize <= LARGE_CONTENT_CAP) {
    const data = await session.lazy.contentByOid(obj.oid);
    if (data) content.set(obj.oid, data);
  }

  const baseOid = obj.baseOid || (raw && raw.baseOid) || null;
  if (baseOid) {
    const baseEntry = session.byOid.get(baseOid);
    if (baseEntry && baseEntry.declaredSize <= LARGE_CONTENT_CAP) {
      const baseData = await session.lazy.contentByOid(baseOid);
      if (baseData) content.set(baseOid, baseData);
    }
  }

  let entry = null;
  if (raw) {
    const slice = await session.lazy.entryBytes(raw);
    const annotated = annotatePackEntrySlice(slice, raw);
    entry = { index: obj.index, bytes: annotated.bytes, regions: annotated.regions };
  }
  return { content, raw, entry };
}

// --- Object list ----------------------------------------------------------

function refreshList() {
  if (!session) return;
  const author = els.filterAuthor.value;
  const needle = els.filterSearch.value.trim().toLowerCase();
  let objects = session.objects;
  if (needle) {
    objects = objects.filter((obj) => {
      if (!obj.oid) return false;
      if (obj.oid.startsWith(needle)) return true;
      const path = session.pathByOid.get(obj.oid);
      return path != null && path.toLowerCase().includes(needle);
    });
  }
  const rows = queryObjects(objects, {
    oids: author ? session.attribution.byKey.get(author)?.oids || new Set() : null,
    type: els.filterType.value || null,
    deltaType: els.filterDelta.value || null,
    sort: els.filterSort.value,
    reachability: els.filterReach.value || null,
    reachable: session.reachable,
  });
  renderObjectRows(els.objectList, rows, session, { selectedOid: session.selectedOid, limit: LIST_LIMIT });
  const total = session.objects.length;
  let count;
  if (rows.length === total) count = `${total.toLocaleString()} objects`;
  else count = `${rows.length.toLocaleString()} of ${total.toLocaleString()} objects match`;
  if (rows.length > LIST_LIMIT) count += `. Showing the first ${LIST_LIMIT}.`;
  els.objectCount.textContent = count;
}

for (const el of [els.filterType, els.filterDelta, els.filterSort, els.filterReach, els.filterAuthor, els.filterSearch]) {
  el.addEventListener("input", () => refreshList());
}

// --- Navigator tabs: Objects, Paths, Refs --------------------------------

function setNavTab(tab) {
  navTab = tab;
  selectTab(document.querySelector(".nav .tablist"), "tab", tab);
  document.querySelectorAll(".nav-panel").forEach((p) => {
    p.hidden = p.dataset.panel !== tab;
  });
  renderNavPanel();
}

function renderNavPanel() {
  if (!session) return;
  if (navTab === "refs") {
    renderRefs(els.refsList, session);
    const n = session.refs.length;
    els.refsCount.textContent = n ? `${n.toLocaleString()} refs` : "";
  } else if (navTab === "paths") {
    renderPathList();
  }
}

function renderPathList() {
  if (!session.pathEntries) {
    session.pathEntries = session.pathRoot ? walkTree(session.pathRoot, session.byOid, session.contentByOid) : [];
  }
  const matches = searchPaths(session.pathEntries, els.pathSearch.value);
  renderPaths(els.pathsList, matches);
  const total = session.pathEntries.length;
  els.pathsCount.textContent = total
    ? matches.length === total
      ? `${total.toLocaleString()} files in the HEAD tree`
      : `${matches.length.toLocaleString()} of ${total.toLocaleString()} files match`
    : "No commit or tree in this pack to list paths from.";
}

els.pathSearch.addEventListener("input", () => {
  if (session) renderPathList();
});

// --- Main views: Overview and Object -------------------------------------

function setView(next) {
  view = next;
  selectTab(document.querySelector(".view-tabs"), "view", next);
  els.overview.hidden = next !== "overview";
  els.detail.hidden = next !== "object";
}

function renderOverviewView() {
  if (!session) return;
  renderOverview(els.overview, session, { ...overviewState, savedCount });
}

// Mark one tab of a tablist selected, with a roving tabindex.
function selectTab(list, attr, value) {
  for (const tab of list.querySelectorAll('[role="tab"]')) {
    const on = tab.dataset[attr] === value;
    tab.setAttribute("aria-selected", String(on));
    tab.tabIndex = on ? 0 : -1;
  }
}

function wireTablist(list, attr, onSelect) {
  list.addEventListener("click", (event) => {
    const tab = event.target.closest('[role="tab"]');
    if (tab) onSelect(tab.dataset[attr]);
  });
  list.addEventListener("keydown", (event) => {
    const tabs = [...list.querySelectorAll('[role="tab"]')];
    const at = tabs.indexOf(document.activeElement);
    if (at === -1) return;
    let next = null;
    if (event.key === "ArrowRight") next = (at + 1) % tabs.length;
    else if (event.key === "ArrowLeft") next = (at - 1 + tabs.length) % tabs.length;
    else if (event.key === "Home") next = 0;
    else if (event.key === "End") next = tabs.length - 1;
    if (next == null) return;
    event.preventDefault();
    tabs[next].focus();
    onSelect(tabs[next].dataset[attr]);
  });
}

wireTablist(document.querySelector(".nav .tablist"), "tab", setNavTab);
wireTablist(document.querySelector(".view-tabs"), "view", (next) => {
  setView(next);
  if (session) writeUrlState({ packId: session.packId, objectId: next === "object" ? session.selectedOid : null });
});

// --- Navigation (in-app history + URL) ----------------------------------

async function go(oid) {
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
  await showObject(obj);
  updateNavButtons();
}

async function showObject(obj) {
  if (!session) return;
  session.selectedOid = obj?.oid || null;
  session.view = null;
  if (session.large && obj) {
    try {
      session.view = await prefetchView(obj);
    } catch (err) {
      console.error(err);
    }
  }
  renderDetail(els.detail, obj, session);
  els.detail.scrollTop = 0;
  markSelected(els.objectList, session.selectedOid);
  setView("object");
  writeUrlState({ packId: session.packId, objectId: session.selectedOid });
}

function updateNavButtons() {
  els.navBack.disabled = histPos <= 0;
  els.navFwd.disabled = histPos >= hist.length - 1;
}

els.navBack.addEventListener("click", () => {
  if (!session || histPos <= 0) return;
  histPos -= 1;
  showObject(session.byOid.get(hist[histPos]));
  updateNavButtons();
});

els.navFwd.addEventListener("click", () => {
  if (!session || histPos >= hist.length - 1) return;
  histPos += 1;
  showObject(session.byOid.get(hist[histPos]));
  updateNavButtons();
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

els.copyLink.addEventListener("click", () => {
  if (!session) return;
  const objectId = view === "object" ? session.selectedOid : null;
  copyText(packShareUrl(session.packId, objectId), "Link copied.");
});

async function copyText(text, done) {
  try {
    await navigator.clipboard.writeText(text);
    setStatus(els.status, done);
  } catch {
    setStatus(els.status, text);
  }
}

// --- Delegated clicks and metric changes ---------------------------------

els.app.addEventListener("click", (event) => {
  const target = event.target.closest(
    "[data-oid], [data-index], [data-action], [data-author], [data-compare], [data-open], [data-delete]",
  );
  if (!target) return;
  const { dataset } = target;
  if (dataset.oid) {
    event.preventDefault();
    go(dataset.oid);
  } else if (dataset.index != null) {
    const obj = session?.objects[Number(dataset.index)];
    if (obj) showObject(obj);
  } else if (dataset.author != null) {
    filterObjects({ author: dataset.author, type: "blob", sort: "packed" });
  } else if (dataset.compare) {
    compareWith(dataset.compare);
  } else if (dataset.open) {
    openSaved(dataset.open);
  } else if (dataset.delete) {
    deleteSaved(dataset.delete);
  } else if (dataset.action) {
    runAction(dataset.action, target);
  }
});

els.app.addEventListener("change", (event) => {
  const select = event.target.closest("select[data-metric]");
  if (!select) return;
  overviewState[select.dataset.metric] = select.value;
  renderOverviewView();
  els.overview.querySelector(`select[data-metric="${select.dataset.metric}"]`)?.focus();
});

function runAction(action, target) {
  switch (action) {
    case "copy-oid":
      copyText(target.dataset.value, "Object id copied.");
      break;
    case "download":
      downloadObject(target.dataset.value);
      break;
    case "filter-type":
      filterObjects({ type: target.dataset.type });
      break;
    case "show-unreachable":
      filterObjects({ reach: "unreachable" });
      break;
    case "compare":
      startCompare();
      break;
    case "close-compare":
      overviewState.compare = null;
      renderOverviewView();
      break;
    default:
      break;
  }
}

// Reset the object filters to the given ones and show the list.
function filterObjects({ type = "", author = "", reach = "", sort = "offset" }) {
  els.filterType.value = type;
  els.filterDelta.value = "";
  els.filterSearch.value = "";
  els.filterAuthor.value = author;
  els.filterReach.value = reach;
  els.filterSort.value = sort;
  if (author || reach) els.filterAuthor.closest("details").open = true;
  setNavTab("objects");
  refreshList();
  els.objectList.scrollTop = 0;
  els.objectList.querySelector("button")?.focus();
}

// --- Download a loose object ---------------------------------------------

function downloadObject(oid) {
  if (!session) return;
  const obj = session.byOid.get(oid);
  const content = session.contentByOid.get(oid) || session.view?.content?.get(oid);
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

// --- Compare -------------------------------------------------------------

async function startCompare() {
  const rows = await listRepos();
  const choices = rows.filter((r) => r.key !== session.packId);
  if (choices.length === 0) {
    setStatus(els.status, "No other saved packs to compare against.", { error: true });
    return;
  }
  overviewState.compare = { choices };
  renderOverviewView();
}

async function compareWith(key) {
  try {
    setStatus(els.status, "Loading pack to compare…");
    const record = await loadRepo(key);
    if (!record) throw new Error("saved pack not found");
    const { resolved } = await parseAndResolve(record.pack);
    overviewState.compare = {
      diff: diffPacks(session.objects, resolved.objects),
      meta: { aName: session.base, bName: record.base },
    };
    renderOverviewView();
    setStatus(els.status, `Compared with ${record.base}.`);
  } catch (err) {
    reportError(err);
  }
}

// --- Saved packs ---------------------------------------------------------

async function refreshSaved() {
  const rows = await listRepos();
  savedCount = rows.length;
  els.saved.hidden = rows.length === 0;
  renderSaved(els.savedList, rows);
}

async function refreshSavedCount() {
  savedCount = (await listRepos()).length;
}

async function openSaved(key) {
  try {
    setStatus(els.status, "Loading saved pack…");
    await openSavedPack(key);
    setStatus(els.status, `Opened ${session.base}.`);
  } catch (err) {
    reportError(err);
  }
}

async function deleteSaved(key) {
  await deleteRepo(key);
  const { packId } = readUrlState();
  if (packId === key) writeUrlState({ packId: null, objectId: null });
  if (session?.packId === key) closePack();
  await refreshSaved();
}

async function openSavedPack(packId, { objectId = null } = {}) {
  const record = await loadRepo(packId);
  if (!record) throw new Error(`No saved pack "${packId}" in this browser.`);
  if (!record.base.startsWith("file://")) els.repo.value = record.base;
  await refreshSavedCount();
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
    setStatus(els.status, `Restored ${session.objects.length.toLocaleString()} objects from ${session.base}.`);
  } catch (err) {
    reportError(err);
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
  await refreshSaved();
  const { packId } = readUrlState();
  if (packId) await restoreFromUrl();
}

boot().catch((err) => console.error(err));
