/**
 * File viewer: text rendering with line numbers, image preview, and the
 * binary / large-file guards. Owns the object-URL lifecycle for images and
 * exposes dispose() so the controller can free it on close / reload.
 */
import { el } from './dom.js';
import { basename, dirname } from '../pathUtils.js';
import {
  imageMimeType,
  isImagePath,
  isBinaryExtension,
  languageForPath,
  looksBinary,
} from '../language.js';
import { formatBytes } from '../format.js';
import { parseLfsPointer } from '../lfs.js';
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
    dom.viewerHead.hidden = true;
    dom.viewerBody.replaceChildren(dom.viewerPlaceholder);
    dom.viewerPlaceholder.hidden = false;
  }

  /** Reveal the header and show a loading state while bytes are fetched. */
  function beginLoading(path) {
    text = null;
    dom.viewerHead.hidden = false;
    renderFilePath(path);
    if (dom.fileHistoryBtn) dom.fileHistoryBtn.hidden = false;
    dom.fileInfo.textContent = 'Loading…';
    dom.viewerBody.replaceChildren(el('div', 'notice', 'Loading…'));
  }

  function showReadError(message) {
    text = null;
    dom.viewerBody.replaceChildren(el('div', 'notice', `Could not read file: ${message}`));
    dom.fileInfo.textContent = '';
  }

  /**
   * Render fetched bytes, choosing image / binary / text presentation.
   *
   * @param {string} path
   * @param {Uint8Array} bytes
   * @param {{lines?: {start:number, end:number}}} [opts]  initial line selection
   */
  function render(path, bytes, opts = {}) {
    const size = bytes.length;
    dispose();

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
    gutter.addEventListener('click', onGutterClick);
    if (target) applyLineSelection(target, { scroll: true, notify: false });
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
    if (notify && typeof ctx.onLinesChange === 'function') ctx.onLinesChange(text.range);
  }

  /** The path of the text file currently shown, or null. */
  function currentTextPath() {
    return text ? text.path : null;
  }

  function renderImage(path, bytes, size) {
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

  /* ---------------------------------------------------------------- */
  /* Diff view (rendered into the same viewer real estate)            */
  /* ---------------------------------------------------------------- */

  function diffHeader(title, subtitle) {
    dispose();
    text = null;
    dom.viewerHead.hidden = false;
    dom.filePath.replaceChildren(el('span', 'name', title));
    if (dom.fileHistoryBtn) dom.fileHistoryBtn.hidden = true; // a diff isn't a file
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

  return {
    render,
    beginLoading,
    showReadError,
    showPlaceholder,
    showDiffLoading,
    renderDiff,
    applyLineSelection,
    currentTextPath,
    dispose,
  };
}
