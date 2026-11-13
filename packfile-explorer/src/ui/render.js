// HTML rendering for the packfile explorer.
//
// Every renderer returns markup or fills one container; none attaches event
// listeners. app.js delegates clicks on `data-*` attributes (data-oid,
// data-index, data-action, data-author, data-compare, data-open, data-delete)
// and changes on `data-metric` selects, once per container.

import { parseCommit, parseTag, parseTree, looksBinary } from "../gitObject.js";
import { parseDelta, buildResolvedSegments, buildBaseSegments } from "../delta.js";
import { annotatePackEntrySlice } from "../packVisual.js";
import { renderHexEditor, renderSegmentedHex, renderSegmentedText } from "../hexView.js";
import { formatBytes, formatPercent, shortOid } from "../format.js";
import { decodeUtf8 } from "../hex.js";
import { buildDeltaChain } from "../deltaChain.js";
import { topObjects } from "../packIndex.js";
import { imageDataUrl } from "../imagePreview.js";
import { BOUNDARY, rankAuthors } from "../attribution.js";

const AUTHOR_COLORS = [
  "#0f6e5c",
  "#e76f51",
  "#457b9d",
  "#e9c46a",
  "#6d597a",
  "#2a9d8f",
  "#f4a261",
  "#8d99ae",
  "#b5838d",
  "#90be6d",
];
const OTHER_COLOR = "#a3b1ad";
const SPECIAL_COLORS = ["#f0d9a8", "#dde4e1"];

const TEXT_PREVIEW_CHARS = 200_000;
const BINARY_PREVIEW_BYTES = 4096;
const DELTA_OPS_SHOWN = 200;

export function setStatus(el, message, { error = false } = {}) {
  el.textContent = message || "";
  el.classList.toggle("error", Boolean(error));
}

// --- Session accessors ----------------------------------------------------

// Object content, resident for small packs or prefetched for the selected
// object in a large pack. Returns null when content is not available.
function contentFor(session, oid) {
  if (!oid) return null;
  if (session.contentByOid && session.contentByOid.has(oid)) {
    return session.contentByOid.get(oid);
  }
  if (session.view && session.view.content) {
    return session.view.content.get(oid) ?? null;
  }
  return null;
}

// The raw pack entry for an object: the full objects array in small packs, or
// the prefetched entry for the selected object in a large pack.
function rawFor(session, obj) {
  if (session.parsed && session.parsed.objects) {
    return session.parsed.objects[obj.index] || null;
  }
  if (session.view && session.view.raw && session.view.raw.index === obj.index) {
    return session.view.raw;
  }
  return null;
}

// Annotated bytes of the object's own pack entry, from the whole pack in
// memory or from the large-pack prefetch.
function packEntryFor(session, obj) {
  if (session.packBytes) {
    const raw = rawFor(session, obj);
    if (!raw) return null;
    const slice = session.packBytes.subarray(raw.offset, raw.offset + raw.packedSize);
    return annotatePackEntrySlice(slice, raw);
  }
  if (session.view && session.view.entry && session.view.entry.index === obj.index) {
    return session.view.entry;
  }
  return null;
}

/**
 * A short human label for an object: its path in the HEAD tree, a commit's
 * subject, or a tag's name. Returns null when there is nothing better than
 * the oid.
 */
function objectLabel(session, obj) {
  if (!obj || !obj.oid) return null;
  const path = session.pathByOid?.get(obj.oid);
  if (path != null) return path === "" ? "/" : path;
  if (obj.typeName === "commit" || obj.typeName === "tag") {
    const content = session.contentByOid?.get(obj.oid);
    if (!content) return null;
    if (obj.typeName === "commit") return commitSubject(content);
    const tag = parseTag(content);
    return tag.tag || null;
  }
  return null;
}

/** First line of a commit message. */
function commitSubject(content) {
  const text = decodeUtf8(content);
  const split = text.indexOf("\n\n");
  if (split === -1) return null;
  const line = text.slice(split + 2).split("\n", 1)[0].trim();
  return line || null;
}

// --- Navigator ------------------------------------------------------------

export function renderPackTitle(el, session) {
  const name = session.base.replace(/^https?:\/\//, "").replace(/^file:\/\//, "");
  const source = session.base.startsWith("file://")
    ? session.large ? "local file, streamed" : "local file"
    : "fetched";
  el.innerHTML =
    `<p class="pack-name" title="${escapeHtml(session.base)}">${escapeHtml(name)}</p>` +
    `<p class="pack-meta">${session.stats.count.toLocaleString()} objects · ` +
    `${escapeHtml(formatBytes(session.stats.totalPacked))} · ${source}</p>`;
}

/**
 * Fill the object list with at most `limit` rows. Rows carry `data-oid`, or
 * `data-index` for objects without an oid (unresolved thin-pack deltas).
 */
export function renderObjectRows(el, rows, session, { selectedOid = null, limit = 500 } = {}) {
  if (rows.length === 0) {
    el.innerHTML = `<li class="empty-row">No matching objects.</li>`;
    return;
  }
  const parts = [];
  const shown = Math.min(rows.length, limit);
  for (let i = 0; i < shown; i += 1) {
    const obj = rows[i];
    const label = objectLabel(session, obj);
    const key = obj.oid
      ? `data-oid="${escapeHtml(obj.oid)}"`
      : `data-index="${obj.index}"`;
    const current = obj.oid && obj.oid === selectedOid ? ` aria-current="true"` : "";
    const idText = obj.oid ? shortOid(obj.oid) : `@${obj.offset}`;
    const main = label
      ? `<span class="row-label">${escapeHtml(label)}</span><span class="row-sub">${escapeHtml(idText)}</span>`
      : `<span class="row-label mono">${escapeHtml(idText)}</span>`;
    parts.push(
      `<li><button type="button" class="row" ${key}${current}>` +
        typePill(obj.typeName) +
        `<span class="row-main">${main}</span>` +
        `<span class="row-size">${escapeHtml(formatBytes(obj.packedSize))}</span>` +
        `</button></li>`,
    );
  }
  el.innerHTML = parts.join("");
}

/** Move the selected-row marker without rebuilding the list. */
export function markSelected(el, oid) {
  for (const row of el.querySelectorAll('[aria-current="true"]')) {
    row.removeAttribute("aria-current");
  }
  if (!oid) return;
  const row = el.querySelector(`[data-oid="${oid}"]`);
  if (row) {
    row.setAttribute("aria-current", "true");
    row.scrollIntoView({ block: "nearest" });
  }
}

/** Fill the Objects tab's author filter with every credited author. */
export function renderAuthorFilter(select, attribution) {
  select.replaceChildren(new Option("All", ""));
  for (const row of attribution ? attribution.authors : []) {
    const label = row.special ? row.key : row.name;
    select.append(new Option(`${label} (${row.blobs.toLocaleString()})`, row.key));
  }
  select.disabled = !attribution || attribution.authors.length === 0;
}

/** Refs tab: advertised refs, each opening the object it points at. */
export function renderRefs(el, session) {
  const refs = (session.refs || []).slice().sort((a, b) => a.name.localeCompare(b.name));
  if (refs.length === 0) {
    el.innerHTML = `<li class="empty-row">No refs. Local packs don't carry them.</li>`;
    return;
  }
  el.innerHTML = refs
    .map((ref) => {
      const obj = session.byOid.get(ref.oid);
      const head = ref.oid === session.head && ref.name !== "HEAD" ? ` <span class="tag">HEAD</span>` : "";
      const name = `<span class="row-label">${escapeHtml(ref.name)}${head}</span>`;
      const sub = `<span class="row-sub">${escapeHtml(shortOid(ref.oid))}</span>`;
      if (!obj) {
        return `<li><div class="row muted">${typePill("missing")}<span class="row-main">${name}${sub}</span></div></li>`;
      }
      return (
        `<li><button type="button" class="row" data-oid="${escapeHtml(ref.oid)}">` +
        `${typePill(obj.typeName)}<span class="row-main">${name}${sub}</span></button></li>`
      );
    })
    .join("");
}

/** Paths tab: flattened tree entries, each opening its blob. */
export function renderPaths(el, entries, { limit = 2000 } = {}) {
  if (!entries || entries.length === 0) {
    el.innerHTML = `<li class="empty-row">No paths match.</li>`;
    return;
  }
  el.innerHTML = entries
    .slice(0, limit)
    .map((entry) => {
      const size = entry.size != null ? formatBytes(entry.size) : "not in pack";
      const name = `<span class="row-label">${escapeHtml(entry.path)}</span>`;
      if (!entry.inPack) {
        return `<li><div class="row muted"><span class="row-main">${name}</span><span class="row-size">${size}</span></div></li>`;
      }
      return (
        `<li><button type="button" class="row" data-oid="${escapeHtml(entry.oid)}">` +
        `<span class="row-main">${name}</span><span class="row-size">${escapeHtml(size)}</span></button></li>`
      );
    })
    .join("");
}

// --- Landing --------------------------------------------------------------

export function renderSaved(el, list) {
  el.innerHTML = list
    .map(
      (row) =>
        `<li><div class="saved-info"><span class="saved-name">${escapeHtml(row.base)}</span>` +
        `<span class="muted">${escapeHtml(formatBytes(row.packBytes))} · ${row.refCount} refs · ` +
        `${escapeHtml(new Date(row.savedAt).toLocaleString())}</span></div>` +
        `<div class="saved-actions">` +
        `<button type="button" class="primary" data-open="${escapeHtml(row.key)}">Open</button>` +
        `<button type="button" data-delete="${escapeHtml(row.key)}">Delete</button>` +
        `</div></li>`,
    )
    .join("");
}

// --- Overview -------------------------------------------------------------

/**
 * Overview: headline numbers, then cards for types, largest objects, blob
 * authors, delta depth, reachability, and the pack trailer. `state` holds
 * `{ metric, authorMetric, savedCount, compare }`.
 */
export function renderOverview(el, session, state) {
  const { stats } = session;
  const deltas = (stats.deltaCounts.ofs || 0) + (stats.deltaCounts.ref || 0);
  const figures = [
    ["Objects", stats.count.toLocaleString()],
    ["Packed", formatBytes(stats.totalPacked)],
    ["Inflated", formatBytes(stats.totalInflated)],
    ["Packed ÷ inflated", formatPercent(stats.compression)],
    ["Deltas", `${deltas.toLocaleString()} (${formatPercent(stats.count ? deltas / stats.count : 0)})`],
    ["Max delta depth", String(stats.maxDepth)],
  ];
  const unresolved = session.unresolved?.length || 0;
  if (unresolved > 0) figures.push(["Unresolved", unresolved.toLocaleString()]);

  el.innerHTML =
    `<div class="view-inner">` +
    `<h2 class="view-title">Overview</h2>` +
    `<dl class="figures">${figures
      .map(([k, v]) => `<div><dt>${escapeHtml(k)}</dt><dd>${escapeHtml(v)}</dd></div>`)
      .join("")}</dl>` +
    `<div class="cards">` +
    typesCard(session) +
    largestCard(session, state.metric || "packed") +
    authorCard(session.attribution, state.authorMetric || "packed") +
    depthCard(stats) +
    reachCard(session) +
    packCard(session, state) +
    (state.compare ? compareCard(state.compare) : "") +
    `</div></div>`;
}

function card(title, body, { wide = false, actions = "" } = {}) {
  return (
    `<section class="card${wide ? " wide" : ""}">` +
    `<div class="card-head"><h3>${escapeHtml(title)}</h3>${actions}</div>${body}</section>`
  );
}

function typesCard(session) {
  const { stats } = session;
  const rows = stats.byType.map((t) => {
    const share = stats.totalPacked > 0 ? t.packed / stats.totalPacked : 0;
    return (
      `<tr><th scope="row"><button type="button" class="linkish" data-action="filter-type" data-type="${escapeHtml(t.type)}">` +
      `${typePill(t.type)}</button></th>` +
      `<td>${t.count.toLocaleString()}</td>` +
      `<td>${escapeHtml(formatBytes(t.packed))}</td>` +
      `<td class="bar-cell">${bar(share, `t-${t.type}`)}<span>${escapeHtml(formatPercent(share))}</span></td></tr>`
    );
  });
  return card(
    "Object types",
    `<table class="data"><caption class="sr-only">Objects by type</caption>` +
      `<thead><tr><th scope="col" class="start">Type</th><th scope="col">Count</th><th scope="col">Packed</th>` +
      `<th scope="col">Share of pack</th></tr></thead><tbody>${rows.join("")}</tbody></table>`,
  );
}

function largestCard(session, metric) {
  const top = topObjects(session.objects, { metric, limit: 10 });
  const rows = top.map(({ obj, value }) => {
    const label = objectLabel(session, obj);
    const id = obj.oid ? shortOid(obj.oid) : `@${obj.offset}`;
    const name = label
      ? `<span class="cell-label">${escapeHtml(label)}</span><span class="cell-sub">${escapeHtml(id)}</span>`
      : `<span class="cell-label mono">${escapeHtml(id)}</span>`;
    const target = obj.oid ? `data-oid="${escapeHtml(obj.oid)}"` : `data-index="${obj.index}"`;
    return (
      `<tr><td class="start">${typePill(obj.typeName)}</td>` +
      `<th scope="row"><button type="button" class="linkish cell-stack" ${target}>${name}</button></th>` +
      `<td>${escapeHtml(metric === "depth" ? String(value) : formatBytes(value))}</td></tr>`
    );
  });
  const select =
    `<label class="metric">Rank by <select data-metric="metric">` +
    metricOption("packed", "packed size", metric) +
    metricOption("inflated", "inflated size", metric) +
    metricOption("savings", "delta savings", metric) +
    metricOption("depth", "delta depth", metric) +
    `</select></label>`;
  return card(
    "Largest objects",
    `<table class="data"><caption class="sr-only">Top objects by ${escapeHtml(metric)}</caption>` +
      `<thead><tr><th scope="col" class="start">Type</th><th scope="col" class="start">Object</th><th scope="col">Value</th></tr></thead>` +
      `<tbody>${rows.join("")}</tbody></table>`,
    { actions: select },
  );
}

function authorCard(attribution, metric) {
  if (!attribution || attribution.totalBlobs === 0) {
    return card("Blobs by author", `<p class="empty">No blobs in this pack.</p>`);
  }
  const select =
    `<label class="metric">Rank by <select data-metric="authorMetric">` +
    metricOption("packed", "packed size", metric) +
    metricOption("inflated", "inflated size", metric) +
    metricOption("blobs", "blob count", metric) +
    `</select></label>`;

  const { top, other, special, total } = rankAuthors(attribution, { metric, limit: 10 });
  const slices = top.map(({ row, value }, i) => ({ row, value, color: AUTHOR_COLORS[i] }));
  if (other.count > 0) {
    slices.push({
      row: null,
      label: `${other.count} other author${other.count === 1 ? "" : "s"}`,
      value: other.value,
      color: OTHER_COLOR,
    });
  }
  special.forEach(({ row, value }, i) => slices.push({ row, value, color: SPECIAL_COLORS[i] }));

  const show = (value) => (metric === "blobs" ? value.toLocaleString() : formatBytes(value));
  const share = (value) => (total > 0 ? formatPercent(value / total) : "—");

  let at = 0;
  const stops = slices.map((slice) => {
    at += total > 0 ? (slice.value / total) * 100 : 0;
    return `${slice.color} 0 ${at.toFixed(3)}%`;
  });

  const rows = slices.map((slice) => {
    const swatch = `<span class="swatch" style="background:${slice.color}"></span>`;
    let who;
    if (!slice.row) {
      who = `<span class="author-name muted">${escapeHtml(slice.label)}</span>`;
    } else {
      const name = slice.row.special ? `<em>${escapeHtml(slice.row.key)}</em>` : escapeHtml(slice.row.name);
      const email =
        slice.row.email && slice.row.email !== slice.row.name
          ? `<span class="author-email">${escapeHtml(slice.row.email)}</span>`
          : "";
      who =
        `<button type="button" class="author-name linkish" data-author="${escapeHtml(slice.row.key)}" ` +
        `title="List ${slice.row.blobs.toLocaleString()} blobs">${name}${email}</button>`;
    }
    return (
      `<tr><th scope="row"><span class="author-cell">${swatch}${who}</span></th>` +
      `<td>${escapeHtml(show(slice.value))}</td><td>${escapeHtml(share(slice.value))}</td></tr>`
    );
  });

  const note = attribution.byKey.has(BOUNDARY)
    ? `<p class="note">${escapeHtml(BOUNDARY)} is every blob in the trees of the oldest fetched ` +
      `commits, whose parents aren't in this pack. Fetch more depth or open a full pack to credit ` +
      `those to authors.</p>`
    : "";

  return card(
    "Blobs by author",
    `<div class="author-layout">` +
      `<div class="author-pie" aria-hidden="true" style="background: conic-gradient(${stops.join(", ")})"></div>` +
      `<table class="data author-table"><caption class="sr-only">Blob ${escapeHtml(metricLabel(metric))} by commit author</caption>` +
      `<thead><tr><th scope="col" class="start">Author</th><th scope="col">${escapeHtml(metricLabel(metric))}</th>` +
      `<th scope="col">Share</th></tr></thead><tbody>${rows.join("")}</tbody></table>` +
      `</div>${note}`,
    { wide: true, actions: select },
  );
}

function depthCard(stats) {
  const maxCount = stats.depthHistogram.reduce((m, d) => Math.max(m, d.count), 1);
  const rows = stats.depthHistogram.map(
    (d) =>
      `<tr><th scope="row">${d.depth === 0 ? "0 (whole)" : d.depth}</th>` +
      `<td class="bar-cell">${bar(d.count / maxCount, "t-depth")}<span>${d.count.toLocaleString()}</span></td></tr>`,
  );
  return card(
    "Delta depth",
    `<table class="data"><caption class="sr-only">Objects by delta chain depth</caption>` +
      `<thead><tr><th scope="col" class="start">Depth</th><th scope="col">Objects</th></tr></thead>` +
      `<tbody>${rows.join("")}</tbody></table>`,
  );
}

function reachCard(session) {
  if (!session.reachable) {
    return card("Reachability", `<p class="empty">No refs to walk from. Local packs don't carry refs.</p>`);
  }
  const total = session.byOid.size;
  const reach = session.reachable.size;
  const orphan = total - reach;
  const body =
    `<p class="big-number">${reach.toLocaleString()} <span class="muted">of ${total.toLocaleString()} reachable</span></p>` +
    bar(total ? reach / total : 0, "t-commit") +
    (orphan > 0
      ? `<p><button type="button" data-action="show-unreachable">List ${orphan.toLocaleString()} unreachable</button></p>`
      : `<p class="muted">Every object is reachable from the fetched refs.</p>`);
  return card("Reachability", body);
}

function packCard(session, state) {
  let checksum = `<span class="mono">${escapeHtml(shortOid(session.parsed.trailer))}</span>`;
  if (session.trailer) {
    checksum =
      `<span class="mono">${escapeHtml(shortOid(session.trailer.storedTrailer))}</span> ` +
      (session.trailer.valid
        ? `<span class="badge ok">valid</span>`
        : `<span class="badge bad">mismatch</span>`);
  } else if (session.large) {
    checksum += ` <span class="badge">not verified</span>`;
  }
  const facts =
    `<dl class="facts">` +
    fact("Version", String(session.parsed.version)) +
    fact("Header count", session.parsed.count.toLocaleString()) +
    fact("Checksum", checksum) +
    fact("Source", escapeHtml(session.base)) +
    `</dl>`;
  const compare =
    state.savedCount > 1 && !session.large
      ? `<p><button type="button" data-action="compare">Compare with another saved pack</button></p>`
      : "";
  const progress = session.progress
    ? `<details class="disclosure"><summary>Server progress</summary><pre class="progress-log">${escapeHtml(session.progress)}</pre></details>`
    : "";
  return card("Pack", facts + compare + progress);
}

function compareCard(compare) {
  if (compare.choices) {
    const body =
      `<ul class="choice-list">${compare.choices
        .map(
          (row) =>
            `<li><button type="button" data-compare="${escapeHtml(row.key)}">${escapeHtml(row.base)}</button></li>`,
        )
        .join("")}</ul>`;
    return card("Compare with", body, { wide: true, actions: closeCompare() });
  }
  const { diff, meta } = compare;
  const facts =
    `<dl class="facts">` +
    fact("Objects", `${diff.a.count} → ${diff.b.count} (${signed(diff.countDelta)})`) +
    fact("Packed", `${formatBytes(diff.a.packed)} → ${formatBytes(diff.b.packed)} (${signedBytes(diff.packedDelta)})`) +
    fact(
      "Inflated",
      `${formatBytes(diff.a.inflated)} → ${formatBytes(diff.b.inflated)} (${signedBytes(diff.inflatedDelta)})`,
    ) +
    fact("In both", diff.common.toLocaleString()) +
    `</dl>`;
  return card(
    `${shortName(meta.aName)} → ${shortName(meta.bName)}`,
    facts + `<div class="diff-cols">${diffList("Added", diff.added)}${diffList("Removed", diff.removed)}</div>`,
    { wide: true, actions: closeCompare() },
  );
}

function closeCompare() {
  return `<button type="button" data-action="close-compare">Close</button>`;
}

function diffList(title, rows) {
  const items = rows.slice(0, 100).map(
    (r) =>
      `<li>${typePill(r.typeName)}<button type="button" class="linkish mono" data-oid="${escapeHtml(r.oid)}">` +
      `${escapeHtml(shortOid(r.oid))}</button><span class="muted">${escapeHtml(formatBytes(r.packedSize))}</span></li>`,
  );
  const more = rows.length > 100 ? `<li class="muted">${rows.length - 100} more</li>` : "";
  return (
    `<div><h4>${title} (${rows.length.toLocaleString()})</h4>` +
    (rows.length ? `<ul class="diff-list">${items.join("")}${more}</ul>` : "") +
    `</div>`
  );
}

// --- Object detail --------------------------------------------------------

export function renderDetail(el, obj, session) {
  if (!obj) {
    el.innerHTML = `<div class="view-inner"><p class="empty">Pick an object from the list.</p></div>`;
    return;
  }

  const content = contentFor(session, obj.oid);
  const raw = rawFor(session, obj);
  const label = objectLabel(session, obj);
  const parts = [`<div class="view-inner">`];

  parts.push(
    `<header class="obj-head">` +
      `<div class="obj-title-row">${typePill(obj.typeName)}` +
      `<h2 class="obj-title">${escapeHtml(label || shortOid(obj.oid) || `entry @${obj.offset}`)}</h2></div>` +
      `<div class="obj-id-row"><code class="oid">${escapeHtml(obj.oid || "no oid: unresolved delta")}</code>` +
      (obj.oid ? `<button type="button" class="small" data-action="copy-oid" data-value="${escapeHtml(obj.oid)}">Copy oid</button>` : "") +
      (content && obj.oid ? `<button type="button" class="small" data-action="download" data-value="${escapeHtml(obj.oid)}">Download loose object</button>` : "") +
      `</div>` +
      `</header>`,
  );

  parts.push(`<dl class="facts obj-facts">`);
  parts.push(fact("Stored as", storedAs(obj)));
  parts.push(fact("Pack offset", obj.offset.toLocaleString()));
  parts.push(fact("Inflated", sizeText(obj.size)));
  parts.push(fact("Packed", sizeText(obj.packedSize)));
  if (obj.baseOid) {
    parts.push(fact("Delta base", oidLink(obj.baseOid)));
  } else if (obj.baseOffset != null) {
    const base = session.byOffset?.get(obj.baseOffset);
    parts.push(
      fact("Delta base", base && base.oid ? oidLink(base.oid) : `@${obj.baseOffset.toLocaleString()}`),
    );
  }
  if (session.reachable && obj.oid) {
    parts.push(
      fact(
        "Reachable",
        session.reachable.has(obj.oid)
          ? `<span class="badge ok">yes</span>`
          : `<span class="badge bad">no</span>`,
      ),
    );
  }
  parts.push(`</dl>`);

  let deltaParsed = null;
  let deltaBaseOid = null;
  let deltaError = null;
  if (raw && (raw.type === 6 || raw.type === 7)) {
    try {
      deltaParsed = parseDelta(raw.data);
      deltaBaseOid = obj.baseOid || raw.baseOid || null;
    } catch (err) {
      deltaError = err.message;
    }
  }

  parts.push(contentSection(obj, content, session, { deltaParsed, deltaBaseOid }));

  if (obj.deltaType !== "none") {
    parts.push(deltaSection(obj, session, { raw, deltaParsed, deltaBaseOid, deltaError }));
  }

  const entry = packEntryFor(session, obj);
  if (entry) {
    parts.push(
      `<details class="disclosure"><summary>Pack entry bytes <span class="muted">(${entry.bytes.length.toLocaleString()} B at offset ${obj.offset.toLocaleString()})</span></summary>` +
        renderHexEditor(entry.bytes, entry.regions, { baseOffset: obj.offset }) +
        `</details>`,
    );
  }

  parts.push(`</div>`);
  el.innerHTML = parts.join("");
}

function storedAs(obj) {
  if (obj.deltaType === "none") return "whole object";
  return `${obj.deltaType}-delta, depth ${obj.depth}`;
}

function sizeText(n) {
  return `${escapeHtml(formatBytes(n))} <span class="muted">(${n.toLocaleString()} B)</span>`;
}

function contentSection(obj, content, session, { deltaParsed, deltaBaseOid }) {
  if (!content) {
    if (obj.typeName === "unresolved") {
      return section("Content", `<p class="empty">Unresolved. This delta's base isn't in the pack (a thin pack).</p>`);
    }
    if (session.large && session.contentCap && obj.size > session.contentCap) {
      return section(
        "Content",
        `<p class="empty">Not loaded. Objects over ${escapeHtml(formatBytes(session.contentCap))} show metadata only.</p>`,
      );
    }
    return section("Content", `<p class="empty">Content isn't available.</p>`);
  }

  if (obj.typeName === "commit") return commitSection(parseCommit(content));
  if (obj.typeName === "tree") return treeSection(parseTree(content), session);
  if (obj.typeName === "tag") return tagSection(parseTag(content));

  const parts = [];
  const dataUrl = imageDataUrl(content);
  if (dataUrl) {
    parts.push(`<div class="image-preview"><img alt="" src="${dataUrl}" /></div>`);
  }
  const binary = looksBinary(content);
  if (deltaParsed) {
    const segments = buildResolvedSegments(deltaParsed, deltaBaseOid);
    parts.push(
      `<p class="note">Colored bytes were copied from the delta base. White bytes are literal inserts.</p>`,
    );
    parts.push(binary ? renderSegmentedHex(content, segments) : renderSegmentedText(content, segments));
  } else if (binary) {
    if (!dataUrl) parts.push(renderHexEditor(content, [], { maxBytes: BINARY_PREVIEW_BYTES }));
  } else {
    const text = decodeUtf8(content);
    const shown =
      text.length > TEXT_PREVIEW_CHARS
        ? `${text.slice(0, TEXT_PREVIEW_CHARS)}\n… truncated at ${TEXT_PREVIEW_CHARS.toLocaleString()} characters`
        : text;
    parts.push(`<pre class="content">${escapeHtml(shown)}</pre>`);
  }
  const kind = dataUrl ? "Image" : binary ? "Binary" : "Text";
  return section(`${kind} · ${formatBytes(content.length)}`, parts.join(""));
}

function commitSection(commit) {
  const text = commit.message.replace(/\s+$/, "");
  const nl = text.indexOf("\n");
  const subject = nl === -1 ? text : text.slice(0, nl);
  const body = nl === -1 ? "" : text.slice(nl + 1).replace(/^\n+/, "");
  const parts = [`<p class="commit-subject">${escapeHtml(subject || "(no message)")}</p>`];
  if (body) parts.push(`<pre class="commit-body">${escapeHtml(body)}</pre>`);
  parts.push(`<dl class="facts">`);
  if (commit.author) parts.push(fact("Author", identityHtml(commit.author)));
  if (commit.committer && commit.committer.raw !== commit.author?.raw) {
    parts.push(fact("Committer", identityHtml(commit.committer)));
  }
  if (commit.tree) parts.push(fact("Tree", oidLink(commit.tree)));
  if (commit.parents.length === 0) parts.push(fact("Parents", `<span class="muted">none (root commit)</span>`));
  else parts.push(fact(commit.parents.length === 1 ? "Parent" : "Parents", commit.parents.map(oidLink).join(" ")));
  parts.push(`</dl>`);
  return section("Commit", parts.join(""));
}

function tagSection(tag) {
  const parts = [`<dl class="facts">`];
  parts.push(fact("Name", escapeHtml(tag.tag || "")));
  if (tag.object) parts.push(fact("Points at", `${oidLink(tag.object)} <span class="muted">${escapeHtml(tag.type || "")}</span>`));
  if (tag.tagger) parts.push(fact("Tagger", identityHtml(tag.tagger)));
  parts.push(`</dl>`);
  if (tag.message) parts.push(`<pre class="commit-body">${escapeHtml(tag.message)}</pre>`);
  return section("Tag", parts.join(""));
}

const ENTRY_KIND = {
  tree: "dir",
  commit: "submodule",
};

function entryKind(entry) {
  if (ENTRY_KIND[entry.type]) return ENTRY_KIND[entry.type];
  if (entry.mode === "120000") return "link";
  if (entry.mode === "100755") return "exec";
  return "file";
}

function treeSection(entries, session) {
  const rows = entries.map((entry) => {
    const target = session.byOid.get(entry.oid);
    const name = target
      ? `<button type="button" class="linkish" data-oid="${escapeHtml(entry.oid)}">${escapeHtml(entry.name)}${entry.type === "tree" ? "/" : ""}</button>`
      : `<span class="muted" title="Not in this pack">${escapeHtml(entry.name)}${entry.type === "tree" ? "/" : ""}</span>`;
    const size = target && entry.type !== "tree" ? formatBytes(target.size) : "";
    return (
      `<tr><td class="muted">${entryKind(entry)}</td><th scope="row">${name}</th>` +
      `<td>${escapeHtml(size)}</td><td class="mono muted">${escapeHtml(shortOid(entry.oid))}</td></tr>`
    );
  });
  return section(
    `Tree · ${entries.length.toLocaleString()} entries`,
    `<table class="data tree-table"><caption class="sr-only">Tree entries</caption>` +
      `<thead><tr><th scope="col" class="start">Kind</th><th scope="col" class="start">Name</th><th scope="col">Size</th><th scope="col" class="start">Object</th></tr></thead>` +
      `<tbody>${rows.join("")}</tbody></table>`,
  );
}

function deltaSection(obj, session, { raw, deltaParsed, deltaBaseOid, deltaError }) {
  const parts = [];

  if (session.byOffset) {
    const chain = buildDeltaChain(obj, { byOid: session.byOid, byOffset: session.byOffset });
    if (chain.length > 1) {
      const links = chain.map((link, i) => {
        const text = link.oid ? shortOid(link.oid) : `@${link.offset}`;
        const tag = i === 0 ? "base" : `${link.deltaType}Δ`;
        const inner = `<span class="mono">${escapeHtml(text)}</span> <span class="tag">${tag}</span>`;
        if (link.oid && link.oid !== obj.oid) {
          return `<li><button type="button" class="linkish" data-oid="${escapeHtml(link.oid)}">${inner}</button></li>`;
        }
        return `<li aria-current="true">${inner}</li>`;
      });
      parts.push(`<ol class="delta-chain" aria-label="Delta chain, base first">${links.join("")}</ol>`);
    }
  }

  if (deltaError) {
    parts.push(`<p class="error">${escapeHtml(deltaError)}</p>`);
    return section("Delta", parts.join(""));
  }
  if (!deltaParsed || !raw) {
    parts.push(`<p class="empty">Delta bytes aren't loaded for this object.</p>`);
    return section("Delta", parts.join(""));
  }

  let copied = 0;
  let inserted = 0;
  let copies = 0;
  let inserts = 0;
  for (const op of deltaParsed.ops) {
    if (op.type === "copy") {
      copied += op.size;
      copies += 1;
    } else {
      inserted += op.data.length;
      inserts += 1;
    }
  }
  parts.push(
    `<dl class="facts">` +
      fact("Copied from base", `${escapeHtml(formatBytes(copied))} <span class="muted">in ${copies.toLocaleString()} copies</span>`) +
      fact("Inserted", `${escapeHtml(formatBytes(inserted))} <span class="muted">in ${inserts.toLocaleString()} inserts</span>`) +
      fact("Delta size", sizeText(raw.data.length)) +
      `</dl>`,
  );

  const baseLink = deltaBaseOid ? oidLink(deltaBaseOid) : "base";
  const ops = deltaParsed.ops.slice(0, DELTA_OPS_SHOWN).map((op) => {
    if (op.type === "copy") {
      return (
        `<tr><th scope="row">copy #${op.copyIndex}</th>` +
        `<td class="start">${baseLink} <span class="mono">@${op.offset}</span></td>` +
        `<td>${escapeHtml(formatBytes(op.size))}</td></tr>`
      );
    }
    return (
      `<tr><th scope="row">insert</th><td class="start"><code>${escapeHtml(previewBytes(op.data, 48))}</code></td>` +
      `<td>${escapeHtml(formatBytes(op.data.length))}</td></tr>`
    );
  });
  const more =
    deltaParsed.ops.length > DELTA_OPS_SHOWN
      ? `<p class="muted">${(deltaParsed.ops.length - DELTA_OPS_SHOWN).toLocaleString()} more instructions not shown.</p>`
      : "";
  parts.push(
    `<details class="disclosure"><summary>Instructions <span class="muted">(${deltaParsed.ops.length.toLocaleString()})</span></summary>` +
      `<table class="data"><caption class="sr-only">Delta instructions</caption>` +
      `<thead><tr><th scope="col" class="start">Op</th><th scope="col" class="start">Source</th><th scope="col">Size</th></tr></thead>` +
      `<tbody>${ops.join("")}</tbody></table>${more}</details>`,
  );

  parts.push(
    `<details class="disclosure"><summary>Delta stream bytes <span class="muted">(inflated)</span></summary>` +
      renderHexEditor(raw.data, deltaParsed.regions) +
      `</details>`,
  );

  const baseContent = contentFor(session, deltaBaseOid);
  if (baseContent) {
    const baseSegs = buildBaseSegments(deltaParsed);
    const baseRegions = baseSegs.map((seg) => ({
      start: seg.start,
      end: seg.end,
      role: "copy-offset",
      copyIndex: seg.copyIndex,
      label: `copy #${seg.copyIndex} · ${seg.size} B`,
    }));
    const reused = baseSegs.reduce((n, s) => n + s.size, 0);
    const pct = baseContent.length > 0 ? formatPercent(reused / baseContent.length) : "0%";
    parts.push(
      `<details class="disclosure"><summary>Base bytes reused <span class="muted">(${escapeHtml(formatBytes(reused))} of ` +
        `${escapeHtml(formatBytes(baseContent.length))}, ${pct})</span></summary>` +
        `<p class="note">Colored ranges are bytes this delta copies from the base. Grey bytes were dropped.</p>` +
        renderHexEditor(baseContent, baseRegions) +
        `</details>`,
    );
  }

  return section(`Delta from ${deltaBaseOid ? shortOid(deltaBaseOid) : "base"}`, parts.join(""));
}

// --- Shared bits ----------------------------------------------------------

function section(title, body) {
  return `<section class="section"><h3>${escapeHtml(title)}</h3>${body}</section>`;
}

function fact(label, valueHtml) {
  return `<div><dt>${escapeHtml(label)}</dt><dd>${valueHtml}</dd></div>`;
}

function typePill(type) {
  return `<span class="type-pill t-${escapeHtml(type)}">${escapeHtml(type)}</span>`;
}

function bar(fraction, cls) {
  const pct = Math.max(0, Math.min(1, fraction)) * 100;
  return `<span class="bar ${cls}" aria-hidden="true"><span style="inline-size:${pct.toFixed(1)}%"></span></span>`;
}

function oidLink(oid) {
  return `<button type="button" class="linkish mono" data-oid="${escapeHtml(oid)}">${escapeHtml(shortOid(oid))}</button>`;
}

function identityHtml(id) {
  if (!id.name) return escapeHtml(id.raw);
  const when = id.date ? id.date.toISOString().replace("T", " ").replace(/:\d\d\.\d+Z$/, " UTC") : "";
  return (
    `${escapeHtml(id.name)} <span class="muted">&lt;${escapeHtml(id.email)}&gt;</span>` +
    (when ? `<br /><span class="muted">${escapeHtml(when)}</span>` : "")
  );
}

function metricOption(value, label, current) {
  return `<option value="${value}"${value === current ? " selected" : ""}>${label}</option>`;
}

function metricLabel(metric) {
  if (metric === "blobs") return "Blobs";
  if (metric === "inflated") return "Inflated";
  return "Packed";
}

function shortName(base) {
  return base.replace(/^https?:\/\//, "").replace(/^file:\/\//, "");
}

function signed(n) {
  return n > 0 ? `+${n}` : String(n);
}

function signedBytes(n) {
  const sign = n > 0 ? "+" : n < 0 ? "−" : "";
  return `${sign}${formatBytes(Math.abs(n))}`;
}

function previewBytes(bytes, max) {
  let text = decodeUtf8(bytes.subarray(0, max)).replace(/[^\x20-\x7e]/g, "·");
  if (bytes.length > max) text += "…";
  return text;
}

function escapeHtml(value) {
  return String(value)
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;");
}
