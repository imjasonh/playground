/**
 * Command palette: the modal fuzzy file finder with keyboard navigation.
 * Owns its own result list + active index (they are only meaningful while the
 * palette is open) and restores focus to its trigger when it closes.
 */
import { el } from './dom.js';
import { appendMatch } from './highlight.js';
import { fuzzyFilter } from '../fuzzy.js';

const PALETTE_LIMIT = 60;

/**
 * @param {{state: object, dom: Record<string, HTMLElement>, openFile: Function}} ctx
 */
export function createPalette(ctx) {
  const { state, dom } = ctx;
  let returnFocus = null;
  let rows = [];
  let activeIndex = 0;

  function isOpen() {
    return !dom.palette.hidden;
  }

  function open() {
    if (!state.source) return;
    // Remember the trigger so keyboard users land back where they started.
    returnFocus = document.activeElement;
    dom.palette.hidden = false;
    dom.paletteInput.value = '';
    dom.paletteInput.focus();
    render();
  }

  function close() {
    const wasOpen = isOpen();
    dom.palette.hidden = true;
    if (
      wasOpen &&
      returnFocus &&
      typeof returnFocus.focus === 'function' &&
      document.contains(returnFocus)
    ) {
      returnFocus.focus();
    }
    returnFocus = null;
  }

  function render() {
    const query = dom.paletteInput.value.trim();
    const results = fuzzyFilter(query, state.files, { limit: PALETTE_LIMIT });
    rows = results;
    activeIndex = 0;

    const list = dom.paletteResults;
    list.replaceChildren();
    dom.paletteEmpty.hidden = results.length > 0;

    results.forEach((result, index) => {
      const row = el('li', 'palette-row');
      row.dataset.path = result.item;
      if (index === 0) row.classList.add('active');
      appendMatch(row, result, 'pr-name', 'pr-path');
      row.addEventListener('click', () => ctx.openFile(result.item));
      list.appendChild(row);
    });
  }

  function move(delta) {
    const elements = dom.paletteResults.children;
    if (elements.length === 0) return;
    elements[activeIndex]?.classList.remove('active');
    activeIndex = (activeIndex + delta + elements.length) % elements.length;
    const active = elements[activeIndex];
    active.classList.add('active');
    active.scrollIntoView({ block: 'nearest' });
  }

  function onKey(event) {
    if (event.key === 'ArrowDown') {
      event.preventDefault();
      move(1);
    } else if (event.key === 'ArrowUp') {
      event.preventDefault();
      move(-1);
    } else if (event.key === 'Enter') {
      event.preventDefault();
      const row = rows[activeIndex];
      if (row) ctx.openFile(row.item);
    } else if (event.key === 'Escape') {
      event.preventDefault();
      close();
    }
  }

  return { open, close, isOpen, render, onKey };
}
