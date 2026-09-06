// DOM rendering for the packfile explorer.

import { parseCommit, parseTag, parseTree, looksBinary } from "../gitObject.js";
import { parseDelta } from "../delta.js";
import { formatBytes, formatPercent, shortOid } from "../format.js";
import { decodeUtf8 } from "../hex.js";

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

export function renderDetail(el, obj, session, onSelectOid) {
  if (!obj) {
    el.innerHTML = `<p class="empty">Select an object to inspect it.</p>`;
    return;
  }

  const content = obj.oid ? session.contentByOid.get(obj.oid) : null;
  const parts = [];
  parts.push(`<h2>${escapeHtml(obj.typeName)}</h2>`);
  parts.push(
    `<p class="oid-full">${escapeHtml(obj.oid || "(unresolved)")}` +
      (obj.deltaType !== "none"
        ? ` <span class="badge">${escapeHtml(obj.deltaType)}-delta · depth ${obj.depth}</span>`
        : "") +
      `</p>`,
  );

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

  // Delta instructions, if this entry was stored as a delta.
  const raw = session.parsed.objects[obj.index];
  if (raw && (raw.type === 6 || raw.type === 7)) {
    try {
      const delta = parseDelta(raw.data);
      parts.push(`<div class="panel"><h3>Delta instructions</h3><ul class="delta-ops">`);
      for (const op of delta.ops.slice(0, 200)) {
        if (op.type === "copy") {
          parts.push(
            `<li><span>copy</span><span>@${op.offset}</span><span>${formatBytes(op.size)}</span></li>`,
          );
        } else {
          parts.push(
            `<li><span>insert</span><span>${escapeHtml(previewBytes(op.data, 40))}</span><span>${formatBytes(op.data.length)}</span></li>`,
          );
        }
      }
      if (delta.ops.length > 200) {
        parts.push(`<li><span>…</span><span>${delta.ops.length - 200} more</span><span></span></li>`);
      }
      parts.push(`</ul></div>`);
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
    if (looksBinary(content)) {
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
