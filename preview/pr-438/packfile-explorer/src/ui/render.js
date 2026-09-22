// DOM rendering for the packfile explorer.

import { parseCommit, parseTag, parseTree, looksBinary } from "../gitObject.js";
import { parseDelta, buildResolvedSegments, buildBaseSegments } from "../delta.js";
import { annotatePackEntry } from "../packVisual.js";
import {
  renderHexEditor,
  renderSegmentedHex,
  renderSegmentedText,
  COPY_PALETTE,
} from "../hexView.js";
import { formatBytes, formatPercent, shortOid } from "../format.js";
import { decodeUtf8 } from "../hex.js";
import { buildDeltaChain } from "../deltaChain.js";
import { topObjects } from "../packIndex.js";
import { imageDataUrl } from "../imagePreview.js";

export function setStatus(el, message, { error = false } = {}) {
  el.textContent = message || "";
  el.classList.toggle("error", Boolean(error));
}

export function renderStats(el, stats, meta) {
  const items = [
    { label: "Objects", value: String(stats.count) },
    { label: "Packed", value: formatBytes(stats.totalPacked) },
    { label: "Inflated", value: formatBytes(stats.totalInflated) },
    { label: "Ratio", value: formatPercent(stats.compression) },
    { label: "Max depth", value: String(stats.maxDepth) },
    {
      label: "Deltas",
      value: `${stats.deltaCounts.ofs || 0} ofs / ${stats.deltaCounts.ref || 0} ref`,
    },
  ];
  if (meta?.base) {
    items.unshift({ label: "Repo", value: meta.base.replace(/^https?:\/\//, "") });
  }
  el.innerHTML = items
    .map(
      (item) =>
        `<div class="stat"><span class="label">${escapeHtml(item.label)}</span>` +
        `<span class="value">${escapeHtml(item.value)}</span></div>`,
    )
    .join("");
}

export function renderObjectList(el, objects, selectedOid, onSelect) {
  el.innerHTML = "";
  if (objects.length === 0) {
    const empty = document.createElement("li");
    empty.innerHTML = `<button type="button" disabled>No matching objects</button>`;
    el.appendChild(empty);
    return;
  }
  for (const obj of objects) {
    const li = document.createElement("li");
    const btn = document.createElement("button");
    btn.type = "button";
    btn.innerHTML =
      `<span class="type">${escapeHtml(obj.typeName)}</span>` +
      `<span class="oid">${escapeHtml(shortOid(obj.oid) || `ofs ${obj.offset}`)}</span>` +
      `<span class="size">${escapeHtml(formatBytes(obj.packedSize))}</span>`;
    if (obj.oid && obj.oid === selectedOid) btn.setAttribute("aria-current", "true");
    btn.addEventListener("click", () => onSelect(obj));
    li.appendChild(btn);
    el.appendChild(li);
  }
}

export function renderDetail(el, obj, session, handlers = {}) {
  const onSelectOid = handlers.onSelectOid || (() => {});
  const onDownload = handlers.onDownload || null;
  if (!obj) {
    el.innerHTML = `<p class="empty">Select an object to inspect it.</p>`;
    return;
  }

  const content = obj.oid ? session.contentByOid.get(obj.oid) : null;
  let deltaParsed = null;
  let deltaBaseOid = null;
  const parts = [];
  parts.push(`<h2>${escapeHtml(obj.typeName)}</h2>`);
  let reachBadge = "";
  if (session.reachable && obj.oid) {
    reachBadge = session.reachable.has(obj.oid)
      ? ` <span class="badge reach-ok">reachable</span>`
      : ` <span class="badge reach-no">unreachable</span>`;
  }
  parts.push(
    `<p class="oid-full">${escapeHtml(obj.oid || "(unresolved)")}` +
      (obj.deltaType !== "none"
        ? ` <span class="badge">${escapeHtml(obj.deltaType)}-delta · depth ${obj.depth}</span>`
        : "") +
      reachBadge +
      `</p>`,
  );

  if (content && onDownload && obj.oid) {
    parts.push(
      `<div class="obj-actions">` +
        `<button type="button" class="quiet small" data-download="${escapeHtml(obj.oid)}">Download loose object</button>` +
        `</div>`,
    );
  }

  parts.push(`<dl class="kv">`);
  parts.push(kv("Offset", String(obj.offset)));
  parts.push(kv("Packed", `${formatBytes(obj.packedSize)} (${obj.packedSize} B)`));
  parts.push(kv("Inflated", `${formatBytes(obj.size)} (${obj.size} B)`));
  parts.push(kv("Compressed", `${formatBytes(obj.compressedSize)} zlib`));
  parts.push(kv("Raw type", obj.rawTypeName));
  if (obj.baseOid) {
    parts.push(
      kv(
        "Delta base",
        `<a href="#${escapeHtml(obj.baseOid)}" data-oid="${escapeHtml(obj.baseOid)}">${escapeHtml(shortOid(obj.baseOid))}</a>`,
      ),
    );
  } else if (obj.baseOffset != null) {
    parts.push(kv("Base offset", String(obj.baseOffset)));
  }
  parts.push(`</dl>`);

  // Delta chain: root base → … → this object, each a jump link.
  if (obj.deltaType !== "none" && session.byOffset) {
    const chain = buildDeltaChain(obj, { byOid: session.byOid, byOffset: session.byOffset });
    if (chain.length > 1) {
      const links = chain.map((link, i) => {
        const label = link.oid ? shortOid(link.oid) : `ofs ${link.offset}`;
        const tag =
          i === 0
            ? "base"
            : link.deltaType !== "none"
              ? `${link.deltaType}Δ`
              : "";
        const inner = `${escapeHtml(label)}${tag ? ` <span class="chain-tag">${tag}</span>` : ""}`;
        const node =
          link.oid && link.oid !== obj.oid
            ? `<a href="#${escapeHtml(link.oid)}" data-oid="${escapeHtml(link.oid)}">${inner}</a>`
            : `<span class="chain-self">${inner}</span>`;
        return `<li>${node}</li>`;
      });
      parts.push(
        `<div class="panel"><h3>Delta chain (${chain.length})</h3>` +
          `<ol class="delta-chain">${links.join("")}</ol></div>`,
      );
    }
  }

  // Delta visualization: pack entry bytes, delta instruction stream, and op list.
  const raw = session.parsed.objects[obj.index];
  if (raw && (raw.type === 6 || raw.type === 7)) {
    try {
      const deltaParsedResult = parseDelta(raw.data);
      const baseOid = obj.baseOid || raw.baseOid || null;

      if (session.packBytes) {
        const entry = annotatePackEntry(session.packBytes, raw);
        parts.push(
          `<div class="panel"><h3>Pack entry @${raw.offset}</h3>` +
            `<p class="panel-note">Raw bytes in the packfile for this object: header, base pointer, zlib.</p>` +
            renderHexEditor(entry.bytes, entry.regions, { baseOffset: raw.offset }) +
            `</div>`,
        );
      }

      parts.push(
        `<div class="panel"><h3>Delta stream (inflated)</h3>` +
          `<p class="panel-note">Decoded zlib payload: size headers, copy pointers into the base object, literal inserts.</p>` +
          renderHexEditor(raw.data, deltaParsedResult.regions) +
          `</div>`,
      );

      parts.push(`<div class="panel"><h3>Delta instructions</h3><ul class="delta-ops">`);
      for (const op of deltaParsedResult.ops.slice(0, 200)) {
        if (op.type === "copy") {
          const baseLink = baseOid
            ? `<a href="#${escapeHtml(baseOid)}" data-oid="${escapeHtml(baseOid)}">${escapeHtml(shortOid(baseOid))}</a>`
            : "base";
          parts.push(
            `<li><span>copy #${op.copyIndex}</span>` +
              `<span>${baseLink} @${op.offset} · ${formatBytes(op.size)}</span>` +
              `<span>pack +${op.span.start}</span></li>`,
          );
        } else {
          parts.push(
            `<li><span>insert</span><span>${escapeHtml(previewBytes(op.data, 40))}</span>` +
              `<span>${formatBytes(op.data.length)}</span></li>`,
          );
        }
      }
      if (deltaParsedResult.ops.length > 200) {
        parts.push(`<li><span>…</span><span>${deltaParsedResult.ops.length - 200} more</span><span></span></li>`);
      }
      parts.push(`</ul></div>`);

      // Base vs result: color the base bytes this delta reuses; grey the rest.
      const baseContent = baseOid ? session.contentByOid.get(baseOid) : null;
      if (baseContent) {
        const baseSegs = buildBaseSegments(deltaParsedResult);
        const baseRegions = baseSegs.map((seg) => ({
          start: seg.start,
          end: seg.end,
          role: "copy-offset",
          copyIndex: seg.copyIndex,
          label: `copy #${seg.copyIndex} · ${seg.size} B`,
        }));
        const copiedBytes = baseSegs.reduce((n, s) => n + s.size, 0);
        const reusePct = baseContent.length > 0 ? (copiedBytes / baseContent.length) * 100 : 0;
        parts.push(
          `<div class="panel"><h3>Delta base @${baseOid ? shortOid(baseOid) : "?"}</h3>` +
            `<p class="panel-note">Colored ranges are bytes this delta copies from the base ` +
            `(${formatBytes(copiedBytes)} of ${formatBytes(baseContent.length)}, ${reusePct.toFixed(0)}% reused). ` +
            `Grey bytes were dropped.</p>` +
            renderHexEditor(baseContent, baseRegions) +
            `</div>`,
        );
      }

      deltaParsed = deltaParsedResult;
      deltaBaseOid = baseOid;
    } catch (err) {
      parts.push(`<div class="panel"><h3>Delta</h3><p>${escapeHtml(err.message)}</p></div>`);
    }
  }

  if (content && obj.typeName === "commit") {
    const commit = parseCommit(content);
    parts.push(`<div class="panel"><h3>Commit</h3><dl class="kv">`);
    parts.push(
      kv(
        "Tree",
        `<a href="#${escapeHtml(commit.tree)}" data-oid="${escapeHtml(commit.tree)}">${escapeHtml(shortOid(commit.tree))}</a>`,
      ),
    );
    for (const parent of commit.parents) {
      parts.push(
        kv(
          "Parent",
          `<a href="#${escapeHtml(parent)}" data-oid="${escapeHtml(parent)}">${escapeHtml(shortOid(parent))}</a>`,
        ),
      );
    }
    if (commit.author) parts.push(kv("Author", escapeHtml(formatIdentity(commit.author))));
    if (commit.committer) parts.push(kv("Committer", escapeHtml(formatIdentity(commit.committer))));
    parts.push(`</dl><pre class="content">${escapeHtml(commit.message)}</pre></div>`);
  } else if (content && obj.typeName === "tree") {
    const entries = parseTree(content);
    parts.push(`<div class="panel"><h3>Tree (${entries.length})</h3><ul class="tree-list">`);
    for (const entry of entries) {
      parts.push(
        `<li><span>${escapeHtml(entry.mode)}</span>` +
          `<a href="#${escapeHtml(entry.oid)}" data-oid="${escapeHtml(entry.oid)}">${escapeHtml(entry.name)}</a>` +
          `<span>${escapeHtml(shortOid(entry.oid))}</span></li>`,
      );
    }
    parts.push(`</ul></div>`);
  } else if (content && obj.typeName === "tag") {
    const tag = parseTag(content);
    parts.push(`<div class="panel"><h3>Tag</h3><dl class="kv">`);
    parts.push(kv("Name", escapeHtml(tag.tag || "")));
    parts.push(
      kv(
        "Object",
        `<a href="#${escapeHtml(tag.object)}" data-oid="${escapeHtml(tag.object)}">${escapeHtml(shortOid(tag.object))}</a> (${escapeHtml(tag.type || "")})`,
      ),
    );
    if (tag.tagger) parts.push(kv("Tagger", escapeHtml(formatIdentity(tag.tagger))));
    parts.push(`</dl><pre class="content">${escapeHtml(tag.message)}</pre></div>`);
  } else if (content && obj.typeName === "blob") {
    const dataUrl = imageDataUrl(content);
    if (dataUrl) {
      parts.push(
        `<div class="panel"><h3>Image (${formatBytes(content.length)})</h3>` +
          `<div class="image-preview"><img alt="blob preview" src="${dataUrl}" /></div></div>`,
      );
    }
    if (deltaParsed) {
      const segments = buildResolvedSegments(deltaParsed, deltaBaseOid);
      parts.push(`<div class="panel"><h3>Resolved blob</h3>`);
      parts.push(
        `<p class="panel-note">White is literal insert data. Colors are bytes copied from the delta base.</p>`,
      );
      if (looksBinary(content)) {
        parts.push(renderSegmentedHex(content, segments));
      } else {
        parts.push(renderSegmentedText(content, segments));
      }
      parts.push(`</div>`);
    } else if (looksBinary(content)) {
      parts.push(
        `<div class="panel"><h3>Blob</h3><p>Binary (${formatBytes(content.length)}). First 64 bytes: ` +
          `<code>${escapeHtml(hexPreview(content, 64))}</code></p></div>`,
      );
    } else {
      const text = decodeUtf8(content);
      const shown = text.length > 200_000 ? `${text.slice(0, 200_000)}\n… truncated` : text;
      parts.push(`<div class="panel"><h3>Blob</h3><pre class="content">${escapeHtml(shown)}</pre></div>`);
    }
  } else if (!content) {
    parts.push(`<div class="panel"><h3>Content</h3><p>Unresolved (thin-pack base missing from this pack).</p></div>`);
  }

  el.innerHTML = parts.join("");
  el.querySelectorAll("[data-oid]").forEach((a) => {
    a.addEventListener("click", (event) => {
      event.preventDefault();
      onSelectOid(a.getAttribute("data-oid"));
    });
  });
  if (onDownload) {
    el.querySelectorAll("[data-download]").forEach((btn) => {
      btn.addEventListener("click", () => onDownload(btn.getAttribute("data-download")));
    });
  }
}

export function renderSaved(el, list, { onOpen, onDelete }) {
  el.innerHTML = "";
  for (const row of list) {
    const li = document.createElement("li");
    const info = document.createElement("div");
    info.innerHTML =
      `<div>${escapeHtml(row.base)}</div>` +
      `<div class="meta">${formatBytes(row.packBytes)} · ${row.refCount} refs · ` +
      `${new Date(row.savedAt).toLocaleString()}</div>`;
    const actions = document.createElement("div");
    actions.style.display = "flex";
    actions.style.gap = "0.4rem";
    const open = document.createElement("button");
    open.type = "button";
    open.textContent = "Open";
    open.addEventListener("click", () => onOpen(row.key));
    const del = document.createElement("button");
    del.type = "button";
    del.className = "quiet";
    del.textContent = "Delete";
    del.addEventListener("click", () => onDelete(row.key));
    actions.append(open, del);
    li.append(info, actions);
    el.appendChild(li);
  }
}

/**
 * Insights tab: leaderboard, per-type and depth breakdowns, reachability, and
 * the pack trailer. `handlers` provides onSelectOid, onMetricChange,
 * onFilterUnreachable, and onCompare.
 */
export function renderInsights(el, session, state, handlers = {}) {
  const parts = [];
  const metric = state.metric || "packed";

  parts.push(`<div class="panel"><h3>Largest objects</h3>`);
  parts.push(
    `<label class="metric-select">Rank by ` +
      `<select id="metric-select">` +
      metricOption("packed", "packed size", metric) +
      metricOption("inflated", "inflated size", metric) +
      metricOption("savings", "delta savings", metric) +
      metricOption("depth", "delta depth", metric) +
      `</select></label>`,
  );
  const top = topObjects(session.objects, { metric, limit: 12 });
  parts.push(`<ul class="leaderboard">`);
  for (const { obj, value } of top) {
    const label = obj.oid ? shortOid(obj.oid) : `ofs ${obj.offset}`;
    const shown = metric === "depth" ? String(value) : formatBytes(value);
    const link = obj.oid
      ? `<a href="#${escapeHtml(obj.oid)}" data-oid="${escapeHtml(obj.oid)}">${escapeHtml(label)}</a>`
      : escapeHtml(label);
    parts.push(
      `<li><span class="type">${escapeHtml(obj.typeName)}</span>${link}<span class="size">${escapeHtml(shown)}</span></li>`,
    );
  }
  parts.push(`</ul></div>`);

  parts.push(`<div class="panel"><h3>By type</h3><ul class="type-table">`);
  for (const t of session.stats.byType) {
    const share = session.stats.totalPacked > 0 ? (t.packed / session.stats.totalPacked) * 100 : 0;
    parts.push(
      `<li><span class="type">${escapeHtml(t.type)}</span>` +
        `<span>${t.count}</span>` +
        `<span class="size">${formatBytes(t.packed)} (${share.toFixed(0)}%)</span></li>`,
    );
  }
  parts.push(`</ul></div>`);

  parts.push(`<div class="panel"><h3>Delta depth</h3><ul class="depth-hist">`);
  const maxCount = session.stats.depthHistogram.reduce((m, d) => Math.max(m, d.count), 1);
  for (const d of session.stats.depthHistogram) {
    const width = (d.count / maxCount) * 100;
    parts.push(
      `<li><span class="depth-label">${d.depth}</span>` +
        `<span class="depth-bar"><span style="width:${width.toFixed(1)}%"></span></span>` +
        `<span class="size">${d.count}</span></li>`,
    );
  }
  parts.push(`</ul></div>`);

  parts.push(`<div class="panel"><h3>Reachability</h3>`);
  if (session.reachable) {
    const total = session.byOid.size;
    const reach = session.reachable.size;
    const orphan = total - reach;
    parts.push(
      `<p class="panel-note">${reach} of ${total} objects reachable from refs · ` +
        `${orphan} unreachable.</p>`,
    );
    if (orphan > 0) {
      parts.push(`<button type="button" id="show-unreachable" class="quiet small">Show unreachable</button>`);
    }
  } else {
    parts.push(`<p class="panel-note">No refs available to compute reachability (local .pack).</p>`);
  }
  parts.push(`</div>`);

  parts.push(`<div class="panel"><h3>Pack</h3><dl class="kv">`);
  parts.push(kv("Version", String(session.parsed.version)));
  parts.push(kv("Objects", String(session.parsed.count)));
  if (session.trailer) {
    const ok = session.trailer.valid
      ? `<span class="badge reach-ok">valid</span>`
      : `<span class="badge reach-no">MISMATCH</span>`;
    parts.push(kv("Checksum", `${shortOid(session.trailer.storedTrailer)} ${ok}`));
  } else {
    parts.push(kv("Checksum", escapeHtml(shortOid(session.parsed.trailer))));
  }
  parts.push(`</dl>`);
  if (state.savedCount > 1) {
    parts.push(`<button type="button" id="compare-btn" class="quiet small">Compare with another pack…</button>`);
  }
  parts.push(`</div>`);

  el.innerHTML = parts.join("");
  el.querySelectorAll("[data-oid]").forEach((a) => {
    a.addEventListener("click", (event) => {
      event.preventDefault();
      handlers.onSelectOid?.(a.getAttribute("data-oid"));
    });
  });
  el.querySelector("#metric-select")?.addEventListener("change", (e) => {
    handlers.onMetricChange?.(e.target.value);
  });
  el.querySelector("#show-unreachable")?.addEventListener("click", () => handlers.onFilterUnreachable?.());
  el.querySelector("#compare-btn")?.addEventListener("click", () => handlers.onCompare?.());
}

function metricOption(value, label, current) {
  return `<option value="${value}"${value === current ? " selected" : ""}>${label}</option>`;
}

/** Refs tab: advertised refs, each opening the object it points at. */
export function renderRefs(el, session, onSelectOid) {
  el.innerHTML = "";
  const refs = session.refs || [];
  if (refs.length === 0) {
    el.innerHTML = `<li class="empty-row">No refs (local .pack or none advertised).</li>`;
    return;
  }
  const rows = refs
    .slice()
    .sort((a, b) => a.name.localeCompare(b.name));
  for (const ref of rows) {
    const li = document.createElement("li");
    const inPack = session.byOid.has(ref.oid);
    const isHead = ref.oid === session.head;
    li.innerHTML =
      `<span class="ref-name">${escapeHtml(ref.name)}${isHead ? ' <span class="chain-tag">HEAD</span>' : ""}</span>` +
      `<span class="ref-oid ${inPack ? "" : "muted"}">${escapeHtml(shortOid(ref.oid))}</span>`;
    if (inPack) {
      li.classList.add("clickable");
      li.addEventListener("click", () => onSelectOid(ref.oid));
    }
    el.appendChild(li);
  }
}

/** Paths tab: flattened tree entries, each opening its blob. */
export function renderPaths(el, entries, onSelectOid) {
  el.innerHTML = "";
  if (!entries || entries.length === 0) {
    el.innerHTML = `<li class="empty-row">No paths. Open a commit or tree first.</li>`;
    return;
  }
  for (const entry of entries.slice(0, 2000)) {
    const li = document.createElement("li");
    li.innerHTML =
      `<span class="path-name">${escapeHtml(entry.path)}</span>` +
      `<span class="size">${entry.size != null ? formatBytes(entry.size) : "—"}</span>`;
    if (entry.inPack) {
      li.classList.add("clickable");
      li.addEventListener("click", () => onSelectOid(entry.oid));
    } else {
      li.classList.add("muted");
    }
    el.appendChild(li);
  }
}

/** Render a two-pack diff into the detail pane. */
export function renderCompare(el, diff, meta, onSelectOid) {
  const parts = [];
  parts.push(`<h2>Compare packs</h2>`);
  parts.push(
    `<p class="oid-full">${escapeHtml(meta.aName)} → ${escapeHtml(meta.bName)}</p>`,
  );
  parts.push(`<dl class="kv">`);
  parts.push(kv("Objects", `${diff.a.count} → ${diff.b.count} (${signed(diff.countDelta)})`));
  parts.push(
    kv("Packed", `${formatBytes(diff.a.packed)} → ${formatBytes(diff.b.packed)} (${signedBytes(diff.packedDelta)})`),
  );
  parts.push(
    kv("Inflated", `${formatBytes(diff.a.inflated)} → ${formatBytes(diff.b.inflated)} (${signedBytes(diff.inflatedDelta)})`),
  );
  parts.push(kv("Common", String(diff.common)));
  parts.push(`</dl>`);

  parts.push(diffList("Added", diff.added));
  parts.push(diffList("Removed", diff.removed));

  el.innerHTML = parts.join("");
  el.querySelectorAll("[data-oid]").forEach((a) => {
    a.addEventListener("click", (event) => {
      event.preventDefault();
      onSelectOid(a.getAttribute("data-oid"));
    });
  });
}

function diffList(title, rows) {
  if (rows.length === 0) return `<div class="panel"><h3>${title} (0)</h3></div>`;
  const items = rows.slice(0, 100).map((r) => {
    const link = `<a href="#${escapeHtml(r.oid)}" data-oid="${escapeHtml(r.oid)}">${escapeHtml(shortOid(r.oid))}</a>`;
    return (
      `<li><span class="type">${escapeHtml(r.typeName)}</span>${link}` +
      `<span class="size">${formatBytes(r.packedSize)}</span></li>`
    );
  });
  const more = rows.length > 100 ? `<li><span>…</span><span>${rows.length - 100} more</span><span></span></li>` : "";
  return `<div class="panel"><h3>${title} (${rows.length})</h3><ul class="delta-ops">${items.join("")}${more}</ul></div>`;
}

function signed(n) {
  return n > 0 ? `+${n}` : String(n);
}

function signedBytes(n) {
  const sign = n > 0 ? "+" : n < 0 ? "−" : "";
  return `${sign}${formatBytes(Math.abs(n))}`;
}

/** Populate the ref picker with a checkbox per branch/tag. */
export function renderRefPicker(el, refs, head) {
  el.innerHTML = "";
  const rows = refs
    .filter((r) => r.name !== "HEAD")
    .sort((a, b) => a.name.localeCompare(b.name));
  for (const ref of rows) {
    const li = document.createElement("li");
    const id = `pick-${ref.oid.slice(0, 12)}-${ref.name.replace(/[^\w]/g, "")}`;
    const checked = ref.oid === head ? " checked" : "";
    const headTag = ref.oid === head ? ' <span class="chain-tag">HEAD</span>' : "";
    li.innerHTML =
      `<label for="${id}"><input type="checkbox" id="${id}" value="${escapeHtml(ref.oid)}"${checked} />` +
      `<span class="ref-name">${escapeHtml(ref.name)}${headTag}</span>` +
      `<span class="ref-oid">${escapeHtml(shortOid(ref.oid))}</span></label>`;
    el.appendChild(li);
  }
}

function kv(label, valueHtml) {
  return `<dt>${escapeHtml(label)}</dt><dd>${valueHtml}</dd>`;
}

function formatIdentity(id) {
  if (!id.name) return id.raw;
  const when = id.date ? id.date.toISOString().replace("T", " ").replace(/\.\d+Z$/, " UTC") : "";
  return `${id.name} <${id.email}> ${when}`;
}

function previewBytes(bytes, max) {
  const slice = bytes.subarray(0, max);
  let text = decodeUtf8(slice);
  text = text.replace(/[^\x20-\x7e]/g, ".");
  if (bytes.length > max) text += "…";
  return text;
}

function hexPreview(bytes, max) {
  const parts = [];
  const n = Math.min(bytes.length, max);
  for (let i = 0; i < n; i += 1) parts.push(bytes[i].toString(16).padStart(2, "0"));
  return parts.join(" ");
}

function escapeHtml(value) {
  return String(value)
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;");
}
