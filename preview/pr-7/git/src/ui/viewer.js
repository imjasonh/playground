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
    dom.fileInfo.textContent = 'Loading…';
    dom.viewerBody.replaceChildren(el('div', 'notice', 'Loading…'));
  }

  function showReadError(message) {
    dom.viewerBody.replaceChildren(el('div', 'notice', `Could not read file: ${message}`));
    dom.fileInfo.textContent = '';
  }

  /**
   * Render fetched bytes, choosing image / binary / text presentation.
   *
   * @returns {'image'|'binary'|'text'} how the file was presented, so callers
   *   (the editing module) can decide whether to offer an in-place editor.
   */
  function render(path, bytes) {
    const size = bytes.length;
    dispose();

    if (isImagePath(path)) {
      renderImage(path, bytes, size);
      return 'image';
    }

    const binary = isBinaryExtension(path) || looksBinary(bytes);
    if (binary) {
      renderBinaryNotice(path, bytes, size);
      return 'binary';
    }

    renderText(path, bytes, size);
    return 'text';
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

  return { render, beginLoading, showReadError, showPlaceholder, dispose, renderFilePath };
}
