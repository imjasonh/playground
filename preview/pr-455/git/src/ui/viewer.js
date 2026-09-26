/**
 * File viewer: text rendering with line numbers, image preview, and the
 * binary / large-file guards. Owns the object-URL lifecycle for images and
 * exposes dispose() so the controller can free it on close / reload.
 */
import { el } from './dom.js';
import { basename, dirname, resolveSymlinkTarget } from '../pathUtils.js';
import {
  imageMimeType,
  isImagePath,
  isMarkdownPath,
  isBinaryExtension,
  languageForPath,
  looksBinary,
} from '../language.js';
import { formatBytes, shortOid, commitSummary, relativeTime } from '../format.js';
import { parseLfsPointer } from '../lfs.js';
import { renderMarkdown } from '../markdown.js';
import { highlight, grammarForPath, withinHighlightBudget } from '../highlightCode.js';

const MAX_TEXT_BYTES = 2_000_000;
const MAX_TEXT_LINES = 50_000;
// Highlighting builds a span per token; skip it for very large files (where the
// extra DOM costs more than the readability win) and just render plain text.
const MAX_HIGHLIGHT_BYTES = 500_000;
const MAX_HIGHLIGHT_LINES = 5_000;

/**
 * @param {{dom: Record<string, HTMLElement>}} ctx
 */
export function createViewer(ctx) {
  const { dom } = ctx;
  const decoder = new TextDecoder('utf-8', { fatal: false });
  let imageUrl = null;
  // Live handle on the currently-rendered text file, so line linking can
  // re-position the highlight without re-rendering the whole file.
  let text = null;
  // The active file's data backing the header actions (copy / download / open).
  // null whenever no real file is shown (placeholder, diff, or read error).
  let current = null;
  // Remembered Markdown view mode so a Raw/Preview choice sticks across files.
  let markdownMode = 'preview';

  wireActions();
  clearCurrent();

  /** Free the current image object URL, if any. */
  function dispose() {
    if (imageUrl) {
      URL.revokeObjectURL(imageUrl);
      imageUrl = null;
    }
    text = null;
  }

  function showPlaceholder() {
    dispose();
    clearCurrent();
    showBlameButton(false);
    dom.viewerHead.hidden = true;
    dom.viewerBody.replaceChildren(dom.viewerPlaceholder);
    dom.viewerPlaceholder.hidden = false;
  }

  /** Reveal the header and show a loading state while bytes are fetched. */
  function beginLoading(path) {
    text = null;
    clearCurrent();
    dom.viewerHead.hidden = false;
    renderFilePath(path);
    if (dom.fileHistoryBtn) dom.fileHistoryBtn.hidden = false;
    // The file type (and thus whether blame applies) isn't known yet.
    showBlameButton(false);
    dom.fileInfo.textContent = 'Loading…';
    dom.viewerBody.replaceChildren(buildSkeleton());
  }

  function showReadError(message) {
    text = null;
    clearCurrent();
    showBlameButton(false);
    dom.viewerBody.replaceChildren(el('div', 'notice', `Could not read file: ${message}`));
    dom.fileInfo.textContent = '';
  }

  /** Show/hide the Blame action — only meaningful for blame-capable sources. */
  function showBlameButton(visible) {
    if (!dom.fileBlameBtn) return;
    const canBlame = typeof ctx.canBlame === 'function' ? ctx.canBlame() : false;
    dom.fileBlameBtn.hidden = !(visible && canBlame);
  }

  /**
   * Render fetched bytes, choosing image / binary / text presentation.
   *
   * @param {string} path
   * @param {Uint8Array} bytes
   * @param {{lines?: {start:number, end:number}, meta?: object}} [opts]
   *   `lines` is the initial selection; `meta` is the entry classification
   *   (symlink/submodule/file) the controller resolved alongside the bytes.
   */
  function render(path, bytes, opts = {}) {
    const size = bytes.length;
    dispose();
    // Off by default; only the text / Markdown paths below (which render real
    // lines to attribute) turn it back on.
    showBlameButton(false);

    // A symlink's blob content is just the path it points at; show that as a
    // notice rather than rendering the target string as if it were the file.
    if (opts.meta && opts.meta.kind === 'symlink') {
      renderSymlinkNotice(path, bytes, opts.meta);
      return;
    }

    // Checked before the image/binary guards: an LFS-tracked file (even one with
    // an image/binary extension) is committed as a tiny text pointer, so without
    // this we'd try to render the pointer as the file and show garbage.
    const pointer = parseLfsPointer(bytes);
    if (pointer) {
      renderLfsNotice(path, bytes, pointer, size);
      return;
    }

    if (isImagePath(path)) {
      renderImage(path, bytes, size);
      return;
    }

    const binary = isBinaryExtension(path) || looksBinary(bytes);
    if (binary) {
      renderBinaryNotice(path, bytes, size);
      return;
    }

    if (isMarkdownPath(path)) {
      renderMarkdownDoc(path, bytes, size);
      return;
    }

    renderText(path, bytes, size, { lines: opts.lines });
  }

  function renderFilePath(path) {
    const dir = dirname(path);
    dom.filePath.replaceChildren();
    if (dir) {
      dom.filePath.appendChild(el('span', 'dir', `${dir}/`));
    }
    dom.filePath.appendChild(el('span', 'name', basename(path)));
  }

  function renderText(path, bytes, size, { force = false, lines: target = null } = {}) {
    const decoded = decoder.decode(bytes);
    let lines = decoded.split('\n');
    if (lines.length > 1 && lines[lines.length - 1] === '' && decoded.endsWith('\n')) {
      lines = lines.slice(0, -1);
    }

    if (!force && (size > MAX_TEXT_BYTES || lines.length > MAX_TEXT_LINES)) {
      text = null;
      // Bytes are in hand, so download still works; "Copy contents" stays off
      // until the text is actually rendered (via "Show anyway").
      setCurrent(path, bytes, null);
      dom.fileInfo.textContent = `${languageForPath(path)} · ${formatBytes(size)}`;
      const notice = el('div', 'notice');
      notice.appendChild(el('p', null, `Large file (${formatBytes(size)}, ${lines.length} lines).`));
      const btn = el('button', 'btn', 'Show anyway');
      btn.type = 'button';
      btn.addEventListener('click', () => renderText(path, bytes, size, { force: true, lines: target }));
      notice.appendChild(btn);
      dom.viewerBody.replaceChildren(notice);
      return;
    }

    dom.fileInfo.textContent =
      `${languageForPath(path)} · ${lines.length} lines · ${formatBytes(size)}`;
    // Real lines are about to render, so blame can attribute them.
    showBlameButton(true);

    const view = el('div', 'code-view');
    const highlightBand = el('div', 'line-highlight');
    highlightBand.hidden = true;
    highlightBand.setAttribute('aria-hidden', 'true');
    const gutter = el('div', 'gutter');
    gutter.textContent = lines.map((_, i) => i + 1).join('\n');
    gutter.title = 'Click a line number to link to it (Shift-click for a range)';
    const code = el('div', 'code');
    paintCode(code, lines, path, size);
    // Absolute overlay first so it sits behind the (positioned) code text.
    view.append(highlightBand, gutter, code);
    dom.viewerBody.replaceChildren(view);

    text = { path, count: lines.length, view, gutter, code, highlight: highlightBand, range: null };
    // `decoded` keeps the file's exact bytes (incl. any trailing newline) for
    // "Copy contents"; `lines` was trimmed only for display.
    setCurrent(path, bytes, decoded);
    gutter.addEventListener('click', onGutterClick);
    if (target) applyLineSelection(target, { scroll: true, notify: false });
  }

  /**
   * Render a Markdown file with a Preview/Raw toggle. Preview shows safe,
   * offline-rendered HTML; Raw shows the source text. The chosen mode is
   * remembered (`markdownMode`) so it sticks as you move between files.
   */
  function renderMarkdownDoc(path, bytes, size) {
    const source = decoder.decode(bytes);
    text = null; // no line-linking handle for the rendered view
    setCurrent(path, bytes, source); // Copy = raw Markdown, Download = bytes
    showBlameButton(true); // blame attributes the raw Markdown lines
    dom.fileInfo.textContent = `${languageForPath(path)} · ${formatBytes(size)}`;

    const doc = el('div', 'md-doc');
    const toolbar = el('div', 'md-toolbar');
    toolbar.setAttribute('role', 'group');
    toolbar.setAttribute('aria-label', 'Markdown view');
    const previewBtn = el('button', 'md-toggle', 'Preview');
    previewBtn.type = 'button';
    const rawBtn = el('button', 'md-toggle', 'Raw');
    rawBtn.type = 'button';
    toolbar.append(previewBtn, rawBtn);

    const content = el('div', 'md-content');
    doc.append(toolbar, content);
    dom.viewerBody.replaceChildren(doc);

    const show = (mode) => {
      markdownMode = mode;
      const preview = mode === 'preview';
      previewBtn.classList.toggle('active', preview);
      previewBtn.setAttribute('aria-pressed', String(preview));
      rawBtn.classList.toggle('active', !preview);
      rawBtn.setAttribute('aria-pressed', String(!preview));
      if (preview) {
        const body = el('div', 'markdown-body');
        body.innerHTML = renderMarkdown(source);
        content.replaceChildren(body);
      } else {
        const pre = el('pre', 'md-raw');
        pre.textContent = source;
        content.replaceChildren(pre);
      }
    };
    previewBtn.addEventListener('click', () => show('preview'));
    rawBtn.addEventListener('click', () => show('raw'));
    show(markdownMode);
  }

  /** Render code text into `code`, syntax-highlighted unless it's too large. */
  function paintCode(code, lines, path, size) {
    const source = lines.join('\n');
    const grammar = grammarForPath(path);
    // Skip highlighting for plain files, very large files, and files whose lines
    // are long enough that tokenizing could be pathologically slow (minified /
    // generated code) — render them as fast, correct plain text instead.
    if (
      grammar === 'plain' ||
      size > MAX_HIGHLIGHT_BYTES ||
      lines.length > MAX_HIGHLIGHT_LINES ||
      !withinHighlightBudget(lines)
    ) {
      code.textContent = source;
      return;
    }
    const frag = document.createDocumentFragment();
    for (const token of highlight(source, grammar)) {
      if (token.type) frag.appendChild(el('span', `tok-${token.type}`, token.text));
      else frag.appendChild(document.createTextNode(token.text));
    }
    code.replaceChildren(frag);
  }

  /* ---- line linking (highlight + click-to-select) ---------------------- */

  /** Per-line height and top padding of the code column, in CSS pixels. */
  function lineMetrics() {
    const cs = getComputedStyle(text.code);
    return { lineH: parseFloat(cs.lineHeight) || 0, padTop: parseFloat(cs.paddingTop) || 0 };
  }

  function onGutterClick(event) {
    if (!text) return;
    const { lineH, padTop } = lineMetrics();
    if (!lineH) return;
    const clicked = Math.floor((event.offsetY - padTop) / lineH) + 1;
    const line = Math.max(1, Math.min(clicked, text.count));
    // Shift-click extends from the existing anchor into a range.
    const anchor = event.shiftKey && text.range ? text.range.start : line;
    const range = { start: Math.min(anchor, line), end: Math.max(anchor, line) };
    applyLineSelection(range, { scroll: false, notify: true });
  }

  /**
   * Highlight a line range, optionally scroll it into view, and optionally
   * notify the controller so it can sync the URL hash.
   *
   * @param {{start:number, end:number}} range
   * @param {{scroll?: boolean, notify?: boolean}} [opts]
   */
  function applyLineSelection(range, { scroll = false, notify = false } = {}) {
    if (!text) return;
    const start = Math.max(1, Math.min(range.start, text.count));
    const end = Math.max(start, Math.min(range.end, text.count));
    text.range = { start, end };

    const { lineH, padTop } = lineMetrics();
    if (lineH) {
      text.highlight.style.top = `${padTop + (start - 1) * lineH}px`;
      text.highlight.style.height = `${(end - start + 1) * lineH}px`;
      text.highlight.hidden = false;
      if (scroll) {
        // Leave a little context above the target line.
        dom.viewerBody.scrollTop = Math.max(0, padTop + (start - 1) * lineH - lineH * 3);
      }
    }
    // Keep the "Open on host" link pointing at the current selection.
    refreshOpenLink();
    if (notify && typeof ctx.onLinesChange === 'function') ctx.onLinesChange(text.range);
  }

  /** The path of the text file currently shown, or null. */
  function currentTextPath() {
    return text ? text.path : null;
  }

  function renderImage(path, bytes, size) {
    setCurrent(path, bytes, null);
    const blob = new Blob([bytes], { type: imageMimeType(path) });
    imageUrl = URL.createObjectURL(blob);
    dom.fileInfo.textContent = `Image · ${formatBytes(size)}`;
    const wrap = el('div', 'image-view');
    const img = el('img');
    img.src = imageUrl;
    img.alt = path;
    wrap.appendChild(img);
    dom.viewerBody.replaceChildren(wrap);
  }

  function renderBinaryNotice(path, bytes, size) {
    setCurrent(path, bytes, null);
    dom.fileInfo.textContent = `Binary · ${formatBytes(size)}`;
    const notice = el('div', 'notice');
    notice.appendChild(el('p', null, `Binary file — ${formatBytes(size)}.`));
    const btn = el('button', 'btn', 'View as text');
    btn.type = 'button';
    btn.addEventListener('click', () => renderText(path, bytes, size, { force: true }));
    notice.appendChild(btn);
    dom.viewerBody.replaceChildren(notice);
  }

  /**
   * Git LFS pointer: the committed blob is metadata, not the real file (which
   * lives on an LFS server this client never contacts). Show what we know and
   * offer to view the raw pointer text rather than rendering it as the file.
   */
  function renderLfsNotice(path, bytes, pointer, size) {
    setCurrent(path, bytes, null);
    dom.fileInfo.textContent = `Git LFS · ${formatBytes(pointer.size)}`;
    const notice = el('div', 'notice');
    notice.appendChild(
      el(
        'p',
        null,
        `Stored with Git LFS. The real file (${formatBytes(pointer.size)}) lives on an ` +
          'LFS server and is not downloaded by this read-only client.'
      )
    );
    notice.appendChild(el('p', 'lfs-oid', pointer.oid));
    const btn = el('button', 'btn', 'View pointer');
    btn.type = 'button';
    btn.addEventListener('click', () => renderText(path, bytes, size, { force: true }));
    notice.appendChild(btn);
    dom.viewerBody.replaceChildren(notice);
  }

  /**
   * Symlink: the committed blob is the link target path, not file content. Show
   * where it points; copy/download still operate on the (tiny) raw blob.
   */
  function renderSymlinkNotice(path, bytes, meta) {
    const target = (meta && meta.target) || decoder.decode(bytes || new Uint8Array()).trim();
    setCurrent(path, bytes, target);
    dom.fileInfo.textContent = 'Symlink';
    const notice = el('div', 'notice');
    notice.appendChild(
      el('p', null, 'Symbolic link — this entry points to another path in the repository.')
    );

    // Resolve the target (relative to the link's directory) and, when it lands on
    // a file that exists in this tree, offer it as a link that opens that file
    // rather than showing the raw "-> target" text alone.
    const resolved = resolveSymlinkTarget(path, target);
    const fileSet = ctx.state && ctx.state.fileSet;
    const canOpen = Boolean(resolved && fileSet && fileSet.has(resolved));

    const line = el('p', 'symlink-target');
    line.appendChild(el('span', 'sym-arrow', '\u2192 '));
    if (canOpen) {
      const link = el('button', 'sym-link', target);
      link.type = 'button';
      link.title = `Open ${resolved}`;
      link.addEventListener('click', () => {
        if (typeof ctx.openFile === 'function') ctx.openFile(resolved);
      });
      line.appendChild(link);
    } else {
      line.appendChild(el('span', 'sym-path', target || '(empty target)'));
    }
    notice.appendChild(line);
    dom.viewerBody.replaceChildren(notice);
  }

  /**
   * Submodule: a gitlink pinning another repository at a commit. Its objects
   * live in that other repo, not this clone, so there's nothing to read.
   * Rendered directly by the controller (there are no bytes to fetch first).
   */
  function renderSubmodule(path, meta = {}) {
    dispose();
    text = null;
    dom.viewerHead.hidden = false;
    renderFilePath(path);
    if (dom.fileHistoryBtn) dom.fileHistoryBtn.hidden = false;
    showBlameButton(false); // a submodule has no lines to attribute
    // No blob: copy the path, but there's nothing to copy-as-text, download, or
    // open as a file on the host.
    setCurrent(path, null, null, { web: false });
    dom.fileInfo.textContent = 'Submodule';

    const notice = el('div', 'notice');
    notice.appendChild(
      el(
        'p',
        null,
        'Git submodule — a pinned reference to another repository. Its files are ' +
          'not part of this clone.'
      )
    );
    if (meta.url) {
      const line = el('p', null);
      line.appendChild(document.createTextNode('Source: '));
      const href = webUrlForRemote(meta.url);
      if (href) {
        const a = el('a', 'submodule-url', meta.url);
        a.href = href;
        a.target = '_blank';
        a.rel = 'noopener noreferrer';
        line.appendChild(a);
      } else {
        line.appendChild(el('span', 'submodule-url', meta.url));
      }
      notice.appendChild(line);
    }
    if (meta.oid) notice.appendChild(el('p', 'submodule-oid', `Pinned at ${meta.oid}`));
    dom.viewerBody.replaceChildren(notice);
  }

  /** Best-effort https URL for a submodule's remote (so the link is clickable). */
  function webUrlForRemote(url) {
    if (typeof url !== 'string') return null;
    const scp = url.match(/^git@([^:]+):(.+?)(?:\.git)?\/?$/);
    if (scp) return `https://${scp[1]}/${scp[2]}`;
    const m = url.match(/^(?:https?|git|ssh):\/\/(?:[^@/]+@)?([^/]+)\/(.+?)(?:\.git)?\/?$/);
    if (m) return `https://${m[1]}/${m[2]}`;
    return null;
  }

  /* ---------------------------------------------------------------- */
  /* Diff view (rendered into the same viewer real estate)            */
  /* ---------------------------------------------------------------- */

  function diffHeader(title, subtitle) {
    dispose();
    text = null;
    clearCurrent(); // a diff isn't a single file: no copy/download/open
    dom.viewerHead.hidden = false;
    dom.filePath.replaceChildren(el('span', 'name', title));
    if (dom.fileHistoryBtn) dom.fileHistoryBtn.hidden = true; // a diff isn't a file
    showBlameButton(false); // nor blame
    dom.fileInfo.textContent = subtitle || '';
  }

  function showDiffLoading(title, subtitle) {
    diffHeader(title, subtitle);
    dom.viewerBody.replaceChildren(el('div', 'notice', 'Computing diff…'));
  }

  /**
   * Render a changed-files summary; each row lazily loads its per-file line diff
   * via `loadFileDiff(change)` (which resolves to a diff result or {binary:true}).
   */
  function renderDiff({ title, subtitle, changes, loadFileDiff }) {
    diffHeader(title, subtitle);
    const summary = summarizeChanges(changes);
    dom.fileInfo.textContent = subtitle ? `${subtitle} · ${summary}` : summary;

    if (!changes.length) {
      dom.viewerBody.replaceChildren(el('div', 'notice', 'No changes between these refs.'));
      return;
    }
    const list = el('div', 'diff-list');
    for (const change of changes) list.appendChild(buildChangeRow(change, loadFileDiff));
    dom.viewerBody.replaceChildren(list);
  }

  function summarizeChanges(changes) {
    const counts = { added: 0, removed: 0, modified: 0 };
    for (const c of changes) counts[c.status] = (counts[c.status] || 0) + 1;
    const parts = [];
    if (counts.added) parts.push(`${counts.added} added`);
    if (counts.modified) parts.push(`${counts.modified} modified`);
    if (counts.removed) parts.push(`${counts.removed} removed`);
    return parts.join(' · ') || `${changes.length} files`;
  }

  function statusGlyph(status) {
    if (status === 'added') return 'A';
    if (status === 'removed') return 'D';
    return 'M';
  }

  function buildChangeRow(change, loadFileDiff) {
    const wrap = el('div', 'diff-file');
    const head = el('button', 'diff-file-head');
    head.type = 'button';
    head.setAttribute('aria-expanded', 'false');
    head.appendChild(el('span', `diff-badge ${change.status}`, statusGlyph(change.status)));
    head.appendChild(el('span', 'diff-file-path', change.path));
    wrap.appendChild(head);

    const body = el('div', 'diff-file-body');
    body.hidden = true;
    wrap.appendChild(body);

    let loaded = false;
    head.addEventListener('click', async () => {
      const open = body.hidden;
      body.hidden = !open;
      head.setAttribute('aria-expanded', String(open));
      head.classList.toggle('open', open);
      if (!open || loaded) return;
      loaded = true;
      body.replaceChildren(el('div', 'notice', 'Loading diff…'));
      let result;
      try {
        result = await loadFileDiff(change);
      } catch (err) {
        body.replaceChildren(el('div', 'notice', `Diff unavailable: ${err.message}`));
        return;
      }
      if (!body.isConnected) return; // navigated away while loading
      renderFileDiff(body, result);
    });
    return wrap;
  }

  function renderFileDiff(body, result) {
    if (result.binary) {
      body.replaceChildren(el('div', 'notice', 'Binary file — no text diff.'));
      return;
    }
    if (result.truncated) {
      body.replaceChildren(el('div', 'notice', 'File too large to diff.'));
      return;
    }
    if (!result.rows.length) {
      body.replaceChildren(el('div', 'notice', 'No textual changes.'));
      return;
    }
    const rows = el('div', 'diff-rows');
    for (const row of result.rows) {
      const line = el('div', `diff-row ${row.type}`);
      line.appendChild(el('span', 'diff-ln', row.oldLine == null ? '' : String(row.oldLine)));
      line.appendChild(el('span', 'diff-ln', row.newLine == null ? '' : String(row.newLine)));
      const sign = row.type === 'add' ? '+' : row.type === 'del' ? '-' : ' ';
      line.appendChild(el('span', 'diff-text', `${sign} ${row.text}`));
      rows.appendChild(line);
    }
    body.replaceChildren(rows);
  }

  /* ---------------------------------------------------------------- */
  /* Blame view (per-line last-change attribution)                    */
  /* ---------------------------------------------------------------- */

  /** Header + body placeholder while blame is being computed. */
  function showBlameLoading(path) {
    dispose();
    text = null;
    dom.viewerHead.hidden = false;
    renderFilePath(path);
    if (dom.fileHistoryBtn) dom.fileHistoryBtn.hidden = false;
    showBlameButton(true);
    // Keep copy-path available on the file; there are no bytes loaded for blame.
    setCurrent(path, null, null, { web: false });
    dom.fileInfo.textContent = 'Computing blame…';
    dom.viewerBody.replaceChildren(buildSkeleton());
  }

  /**
   * Render per-line blame: each line prefixed with the commit that last changed
   * it. Consecutive lines from the same commit share one chip (as `git blame`
   * does), and a chip click opens that commit's diff via `onOpenCommit`.
   *
   * @param {string} path
   * @param {{line: string, commit: object}[]} rows
   * @param {{onOpenCommit?: (commit: object) => void}} [opts]
   */
  function renderBlame(path, rows, { onOpenCommit } = {}) {
    dispose();
    text = null;
    dom.viewerHead.hidden = false;
    renderFilePath(path);
    if (dom.fileHistoryBtn) dom.fileHistoryBtn.hidden = false;
    showBlameButton(true);
    setCurrent(path, null, null, { web: false });

    const wrap = el('div', 'blame-view');
    const toolbar = el('div', 'blame-toolbar');
    const back = el('button', 'btn ghost small', '\u2190 Back to file');
    back.type = 'button';
    back.addEventListener('click', () => {
      if (typeof ctx.openFile === 'function') ctx.openFile(path);
    });
    toolbar.appendChild(back);
    wrap.appendChild(toolbar);

    if (rows.length > MAX_TEXT_LINES) {
      dom.fileInfo.textContent = `Blame · ${rows.length} lines`;
      wrap.appendChild(el('div', 'notice', 'File is too large to blame.'));
      dom.viewerBody.replaceChildren(wrap);
      return;
    }

    const distinct = new Set(rows.map((r) => r.commit && r.commit.oid)).size;
    dom.fileInfo.textContent =
      `Blame · ${rows.length} lines · ${distinct} commit${distinct === 1 ? '' : 's'}`;

    const grid = el('div', 'blame-rows');
    let prevOid = null;
    rows.forEach((row, i) => {
      const commit = row.commit || {};
      const line = el('div', 'blame-row');
      const chipCell = el('div', 'blame-commit-cell');
      // One chip per contiguous run of the same commit, like git blame.
      if (commit.oid !== prevOid) chipCell.appendChild(buildBlameChip(commit, onOpenCommit));
      line.appendChild(chipCell);
      line.appendChild(el('span', 'blame-ln', String(i + 1)));
      // A non-breaking space keeps blank source lines from collapsing to 0 height.
      line.appendChild(el('span', 'blame-code', row.line === '' ? '\u00a0' : row.line));
      grid.appendChild(line);
      prevOid = commit.oid;
    });
    wrap.appendChild(grid);
    dom.viewerBody.replaceChildren(wrap);
  }

  /** A clickable commit chip for a blame run (opens the commit when possible). */
  function buildBlameChip(commit, onOpenCommit) {
    const chip = el('button', 'blame-commit', shortOid(commit.oid || '') || '—');
    chip.type = 'button';
    const who = commit.author && commit.author.name ? ` · ${commit.author.name}` : '';
    const when = commit.timestamp ? ` · ${relativeTime(commit.timestamp)}` : '';
    const summary = commitSummary(commit.message);
    chip.title = `${summary || shortOid(commit.oid || '')}${who}${when}`;
    if (typeof onOpenCommit === 'function' && commit.oid) {
      chip.addEventListener('click', () => onOpenCommit(commit));
    } else {
      chip.disabled = true;
    }
    return chip;
  }

  /* ---------------------------------------------------------------- */
  /* Header actions (copy path / copy contents / download / open)     */
  /* ---------------------------------------------------------------- */

  function wireActions() {
    if (dom.fileCopyPathBtn) {
      dom.fileCopyPathBtn.addEventListener('click', () =>
        copyToClipboard(current && current.path, 'Path copied')
      );
    }
    if (dom.fileCopyBtn) {
      dom.fileCopyBtn.addEventListener('click', () =>
        copyToClipboard(current && current.text, 'Contents copied')
      );
    }
    if (dom.fileDownloadBtn) dom.fileDownloadBtn.addEventListener('click', downloadCurrent);
    // The Blame button is wired in the controller (next to History, the action
    // it most resembles). Binding it here too would run blame twice per click.
  }

  /**
   * Record the active file backing the header actions. `text` is null when the
   * file can't be copied as text (binary/image/large); `bytes` is null when
   * there's nothing to download (a submodule); `opts.web` is false when the
   * entry has no meaningful "open as a file on the host" target.
   */
  function setCurrent(path, bytes, text, opts = {}) {
    current = {
      path,
      bytes: bytes || null,
      text: text == null ? null : text,
      web: opts.web !== false,
    };
    refreshActions();
  }

  function clearCurrent() {
    current = null;
    refreshActions();
  }

  /** Show/hide each header action to match the active file. */
  function refreshActions() {
    if (dom.fileCopyPathBtn) dom.fileCopyPathBtn.hidden = !(current && current.path);
    if (dom.fileDownloadBtn) dom.fileDownloadBtn.hidden = !(current && current.bytes);
    if (dom.fileCopyBtn) dom.fileCopyBtn.hidden = !(current && current.text != null);
    refreshOpenLink();
  }

  /** Point the "Open" link at the active file on its host, or hide it. */
  function refreshOpenLink() {
    const a = dom.fileOpenBtn;
    if (!a) return;
    let url = null;
    if (current && current.web && typeof ctx.fileWebUrl === 'function') {
      const lines = text && text.path === current.path ? text.range : null;
      url = ctx.fileWebUrl(current.path, lines);
    }
    if (url) {
      const host = hostLabelFromUrl(url);
      a.href = url;
      a.title = `Open on ${host}`;
      a.setAttribute('aria-label', `Open ${basename(current.path)} on ${host}`);
      a.hidden = false;
    } else {
      a.removeAttribute('href');
      a.hidden = true;
    }
  }

  function hostLabelFromUrl(url) {
    try {
      const host = new URL(url).hostname;
      if (host === 'github.com') return 'GitHub';
      if (host === 'bitbucket.org') return 'Bitbucket';
      if (host === 'gitlab.com' || host.startsWith('gitlab.')) return 'GitLab';
      return host;
    } catch {
      return 'the host';
    }
  }

  async function copyToClipboard(value, okMessage) {
    if (value == null) return;
    const clip = typeof navigator !== 'undefined' ? navigator.clipboard : null;
    if (!clip || typeof clip.writeText !== 'function') {
      toast('Clipboard is unavailable in this browser.', 'error');
      return;
    }
    try {
      await clip.writeText(value);
      toast(okMessage, 'success');
    } catch {
      toast('Copy was blocked by the browser.', 'error');
    }
  }

  /** Save the active file's raw bytes to disk via a transient object URL. */
  function downloadCurrent() {
    if (!current || !current.bytes) return;
    const blob = new Blob([current.bytes]);
    const url = URL.createObjectURL(blob);
    const a = el('a');
    a.href = url;
    a.download = basename(current.path) || 'file';
    document.body.appendChild(a);
    a.click();
    a.remove();
    setTimeout(() => URL.revokeObjectURL(url), 0);
  }

  function toast(message, type) {
    if (typeof ctx.toast === 'function') ctx.toast(message, type);
  }

  /** A shimmer placeholder shown while a file's bytes are being fetched. */
  function buildSkeleton() {
    const wrap = el('div', 'skeleton');
    wrap.setAttribute('aria-hidden', 'true');
    // A handful of bars of varied width read as "loading content".
    const widths = [70, 45, 85, 60, 78, 38, 66, 90, 52, 74];
    for (const w of widths) {
      const bar = el('div', 'skeleton-line');
      bar.style.width = `${w}%`;
      wrap.appendChild(bar);
    }
    return wrap;
  }

  return {
    render,
    renderSubmodule,
    beginLoading,
    showReadError,
    showPlaceholder,
    showDiffLoading,
    renderDiff,
    showBlameLoading,
    renderBlame,
    applyLineSelection,
    currentTextPath,
    dispose,
  };
}
