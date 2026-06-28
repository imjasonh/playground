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

const MAX_TEXT_BYTES = 2_000_000;
const MAX_TEXT_LINES = 50_000;

/**
 * @param {{dom: Record<string, HTMLElement>}} ctx
 */
export function createViewer(ctx) {
  const { dom } = ctx;
  const decoder = new TextDecoder('utf-8', { fatal: false });
  let imageUrl = null;

  /** Free the current image object URL, if any. */
  function dispose() {
    if (imageUrl) {
      URL.revokeObjectURL(imageUrl);
      imageUrl = null;
    }
  }

  function showPlaceholder() {
    dispose();
    dom.viewerHead.hidden = true;
    dom.viewerBody.replaceChildren(dom.viewerPlaceholder);
    dom.viewerPlaceholder.hidden = false;
  }

  /** Reveal the header and show a loading state while bytes are fetched. */
  function beginLoading(path) {
    dom.viewerHead.hidden = false;
    renderFilePath(path);
    if (dom.fileHistoryBtn) dom.fileHistoryBtn.hidden = false;
    dom.fileInfo.textContent = 'Loading…';
    dom.viewerBody.replaceChildren(el('div', 'notice', 'Loading…'));
  }

  function showReadError(message) {
    dom.viewerBody.replaceChildren(el('div', 'notice', `Could not read file: ${message}`));
    dom.fileInfo.textContent = '';
  }

  /** Render fetched bytes, choosing image / binary / text presentation. */
  function render(path, bytes) {
    const size = bytes.length;
    dispose();

    if (isImagePath(path)) {
      renderImage(path, bytes, size);
      return;
    }

    const binary = isBinaryExtension(path) || looksBinary(bytes);
    if (binary) {
      renderBinaryNotice(path, bytes, size);
      return;
    }

    renderText(path, bytes, size);
  }

  function renderFilePath(path) {
    const dir = dirname(path);
    dom.filePath.replaceChildren();
    if (dir) {
      dom.filePath.appendChild(el('span', 'dir', `${dir}/`));
    }
    dom.filePath.appendChild(el('span', 'name', basename(path)));
  }

  function renderText(path, bytes, size, { force = false } = {}) {
    const text = decoder.decode(bytes);
    let lines = text.split('\n');
    if (lines.length > 1 && lines[lines.length - 1] === '' && text.endsWith('\n')) {
      lines = lines.slice(0, -1);
    }

    if (!force && (size > MAX_TEXT_BYTES || lines.length > MAX_TEXT_LINES)) {
      dom.fileInfo.textContent = `${languageForPath(path)} · ${formatBytes(size)}`;
      const notice = el('div', 'notice');
      notice.appendChild(el('p', null, `Large file (${formatBytes(size)}, ${lines.length} lines).`));
      const btn = el('button', 'btn', 'Show anyway');
      btn.type = 'button';
      btn.addEventListener('click', () => renderText(path, bytes, size, { force: true }));
      notice.appendChild(btn);
      dom.viewerBody.replaceChildren(notice);
      return;
    }

    dom.fileInfo.textContent =
      `${languageForPath(path)} · ${lines.length} lines · ${formatBytes(size)}`;

    const view = el('div', 'code-view');
    const gutter = el('div', 'gutter');
    gutter.textContent = lines.map((_, i) => i + 1).join('\n');
    const code = el('div', 'code');
    code.textContent = lines.join('\n');
    view.append(gutter, code);
    dom.viewerBody.replaceChildren(view);
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

  /* ---------------------------------------------------------------- */
  /* Diff view (rendered into the same viewer real estate)            */
  /* ---------------------------------------------------------------- */

  function diffHeader(title, subtitle) {
    dispose();
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
    dispose,
  };
}
