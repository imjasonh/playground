// Packfile explorer entry point.
//
// Flow: type a repo → fetch refs + pack through the CORS proxy → parse and
// resolve objects → index them for filtering/stats → persist the raw pack in
// IndexedDB so it can be reopened offline. Shareable URLs use ?pack=<stored id>
// and an optional #<object oid> so refresh restores the same pack and selection.

import pako from "../vendor/pako/pako.esm.mjs";
import { makePakoInflate } from "./inflate.js";
import { parsePack, resolveObjects } from "./pack.js";
import { subtleComputeOid } from "./oid.js";
import { computeStats, queryObjects } from "./packIndex.js";
import { normalizeRepoUrl, DEFAULT_PROXY } from "./proxy.js";
import { fetchPack, fetchRefs } from "./transport.js";
import { deleteRepo, listRepos, loadRepo, saveRepo } from "./store.js";
import { readUrlState, writeUrlState } from "./urlState.js";
import {
  renderDetail,
  renderObjectList,
  renderSaved,
  renderStats,
  setStatus,
} from "./ui/render.js";

const inflate = makePakoInflate(pako);
const computeOid = subtleComputeOid(crypto.subtle);

const els = {
  form: document.getElementById("fetch-form"),
  repo: document.getElementById("repo"),
  deepen: document.getElementById("deepen"),
  fetchBtn: document.getElementById("fetch-btn"),
  status: document.getElementById("status"),
  saved: document.getElementById("saved"),
  savedList: document.getElementById("saved-list"),
  workspace: document.getElementById("workspace"),
  stats: document.getElementById("stats"),
  objectList: document.getElementById("object-list"),
  detail: document.getElementById("detail"),
  filterType: document.getElementById("filter-type"),
  filterDelta: document.getElementById("filter-delta"),
  filterSort: document.getElementById("filter-sort"),
  filterSearch: document.getElementById("filter-search"),
};

/** @type {null | {
 *   packId: string,
 *   base: string,
 *   refs: Array,
 *   head: string | null,
 *   parsed: object,
 *   objects: Array,
 *   byOid: Map,
 *   contentByOid: Map,
 *   stats: object,
 *   selectedOid: string | null,
 * }} */
let session = null;

els.form.addEventListener("submit", async (event) => {
  event.preventDefault();
  await runFetch();
});

document.getElementById("pack-file").addEventListener("change", async (event) => {
  const file = event.target.files && event.target.files[0];
  event.target.value = "";
  if (!file) return;
  try {
    setStatus(els.status, `Reading ${file.name}…`);
    const pack = new Uint8Array(await file.arrayBuffer());
    const base = `file://${file.name}`;
    const record = {
      base,
      refs: [],
      head: null,
      wants: [],
      pack,
      progress: "",
    };
    await openPack(record);
    await saveRepo(record);
    await refreshSaved();
    setStatus(els.status, `Loaded ${session.objects.length} objects from ${file.name}`);
  } catch (err) {
    console.error(err);
    setStatus(els.status, err.message || String(err), { error: true });
  }
});

for (const el of [els.filterType, els.filterDelta, els.filterSort, els.filterSearch]) {
  el.addEventListener("input", () => refreshList());
}

async function runFetch() {
  let base;
  try {
    base = normalizeRepoUrl(els.repo.value);
  } catch (err) {
    setStatus(els.status, err.message, { error: true });
    return;
  }
  const deepen = Math.max(1, Math.min(50, Number(els.deepen.value) || 1));
  els.fetchBtn.disabled = true;
  try {
    setStatus(els.status, `Fetching refs for ${base}…`);
    const refs = await fetchRefs(DEFAULT_PROXY, base);
    const wants = pickWants(refs);
    setStatus(
      els.status,
      `Fetching pack (depth ${deepen}, ${wants.length} want${wants.length === 1 ? "" : "s"})…`,
    );
    const { pack, progress } = await fetchPack(DEFAULT_PROXY, base, { wants, deepen });
    setStatus(els.status, `Parsing ${pack.length.toLocaleString()} pack bytes…`);
    const record = {
      base,
      refs: refs.refs,
      head: refs.head,
      wants,
      pack,
      progress,
    };
    await openPack(record);
    await saveRepo(record);
    await refreshSaved();
    setStatus(
      els.status,
      `Loaded ${session.objects.length} objects from ${base}` +
        (progress ? ` · ${progress.trim().split("\n").pop()}` : ""),
    );
  } catch (err) {
    console.error(err);
    setStatus(els.status, err.message || String(err), { error: true });
  } finally {
    els.fetchBtn.disabled = false;
  }
}

function pickWants(refs) {
  // Prefer HEAD; otherwise every heads ref (so a bare default branch still works).
  if (refs.head) return [refs.head];
  const heads = refs.refs.filter((r) => r.name.startsWith("refs/heads/"));
  if (heads.length > 0) return [heads[0].oid];
  return [refs.refs[0].oid];
}

async function openSavedPack(packId, { objectId = null } = {}) {
  const record = await loadRepo(packId);
  if (!record) {
    throw new Error(`No saved pack "${packId}" in this browser`);
  }
  els.repo.value = record.base;
  await openPack(record, { objectId });
}

async function openPack(record, { objectId = null } = {}) {
  const parsed = parsePack(record.pack, inflate);
  const resolved = await resolveObjects(parsed, computeOid);
  const stats = computeStats(resolved.objects);
  const packId = record.base;
  session = {
    packId,
    base: record.base,
    refs: record.refs,
    head: record.head,
    packBytes: record.pack,
    parsed,
    objects: resolved.objects,
    byOid: resolved.byOid,
    contentByOid: resolved.contentByOid,
    stats,
    selectedOid: null,
  };
  els.saved.hidden = true;
  els.workspace.hidden = false;
  renderStats(els.stats, stats, { base: record.base });

  let initial = null;
  if (objectId && resolved.byOid.has(objectId)) {
    initial = resolved.byOid.get(objectId);
  } else if (record.head && resolved.byOid.has(record.head)) {
    initial = resolved.byOid.get(record.head);
  } else {
    initial = resolved.objects.find((o) => o.typeName === "commit") || resolved.objects[0];
  }
  selectObject(initial || null);
  refreshList();
}

function refreshList() {
  if (!session) return;
  const rows = queryObjects(session.objects, {
    type: els.filterType.value || null,
    deltaType: els.filterDelta.value || null,
    search: els.filterSearch.value,
    sort: els.filterSort.value,
  });
  renderObjectList(els.objectList, rows, session.selectedOid, selectObject);
}

function selectObject(obj) {
  if (!session) {
    renderDetail(els.detail, null, session, selectOid);
    return;
  }
  session.selectedOid = obj?.oid || null;
  renderDetail(els.detail, obj, session, selectOid);
  refreshList();
  writeUrlState({ packId: session.packId, objectId: session.selectedOid });
}

function selectOid(oid) {
  if (!session) return;
  const obj = session.byOid.get(oid);
  if (obj) selectObject(obj);
  else setStatus(els.status, `Object ${oid.slice(0, 8)} is not in this pack.`, { error: true });
}

async function refreshSaved() {
  const rows = await listRepos();
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
        await refreshSaved();
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
        renderDetail(els.detail, null, session, selectOid);
      }
      await refreshSaved();
    },
  });
}

async function restoreFromUrl() {
  const { packId, objectId } = readUrlState();
  if (!packId) return;
  if (session?.packId === packId) {
    if (objectId && session.byOid.has(objectId)) selectObject(session.byOid.get(objectId));
    return;
  }
  try {
    setStatus(els.status, "Restoring pack from link…");
    await openSavedPack(packId, { objectId });
    setStatus(els.status, `Restored ${session.objects.length} objects from ${session.base}`);
    await refreshSaved();
  } catch (err) {
    console.error(err);
    setStatus(els.status, err.message || String(err), { error: true });
    await refreshSaved();
  }
}

window.addEventListener("hashchange", () => {
  const { objectId } = readUrlState();
  if (objectId && session?.byOid.has(objectId)) selectObject(session.byOid.get(objectId));
});

window.addEventListener("popstate", () => {
  void restoreFromUrl();
});

async function boot() {
  const { packId } = readUrlState();
  if (packId) {
    await restoreFromUrl();
  } else {
    await refreshSaved();
  }
}

boot().catch((err) => console.error(err));
