// Packfile explorer entry point.
//
// Flow: type a repo → fetch refs + pack through the CORS proxy → parse and
// resolve objects → index them for filtering/stats → persist the raw pack in
// IndexedDB so it can be reopened offline.

import pako from "../vendor/pako/pako.esm.mjs";
import { makePakoInflate } from "./inflate.js";
import { parsePack, resolveObjects } from "./pack.js";
import { subtleComputeOid } from "./oid.js";
import { computeStats, queryObjects } from "./packIndex.js";
import { normalizeRepoUrl, DEFAULT_PROXY } from "./proxy.js";
import { fetchPack, fetchRefs } from "./transport.js";
import { deleteRepo, listRepos, loadRepo, saveRepo } from "./store.js";
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
    await openPack({
      base: `file://${file.name}`,
      refs: [],
      head: null,
      wants: [],
      pack,
      progress: "",
    });
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
    await openPack({
      base,
      refs: refs.refs,
      head: refs.head,
      wants,
      pack,
      progress,
    });
    await saveRepo({
      base,
      refs: refs.refs,
      head: refs.head,
      wants,
      pack,
      progress,
    });
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

async function openPack(record) {
  const parsed = parsePack(record.pack, inflate);
  const resolved = await resolveObjects(parsed, computeOid);
  const stats = computeStats(resolved.objects);
  session = {
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
  // Prefer opening HEAD so the first clickable surface is a commit, not an ofs.
  const initial = record.head && resolved.byOid.has(record.head)
    ? resolved.byOid.get(record.head)
    : resolved.objects.find((o) => o.typeName === "commit") || resolved.objects[0];
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
  if (!session || !obj) {
    renderDetail(els.detail, null, session, selectOid);
    return;
  }
  session.selectedOid = obj.oid;
  renderDetail(els.detail, obj, session, selectOid);
  refreshList();
  location.hash = obj.oid || "";
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
        const record = await loadRepo(key);
        if (!record) throw new Error("saved pack not found");
        els.repo.value = record.base;
        await openPack(record);
        setStatus(els.status, `Opened saved pack for ${record.base}`);
      } catch (err) {
        setStatus(els.status, err.message, { error: true });
      }
    },
    onDelete: async (key) => {
      await deleteRepo(key);
      await refreshSaved();
    },
  });
}

window.addEventListener("hashchange", () => {
  const oid = location.hash.replace(/^#/, "");
  if (oid && session && session.byOid.has(oid)) selectOid(oid);
});

refreshSaved().catch((err) => console.error(err));
