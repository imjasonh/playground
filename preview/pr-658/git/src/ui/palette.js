/**
 * Command palette: the modal fuzzy file finder with keyboard navigation.
 *
 * The result list is virtualized, so the active selection is tracked as a
 * logical index into the full result set rather than by walking rendered DOM
 * children: navigating scrolls the active row into view and repaints the
 * window. Owns its own state and restores focus to its trigger on close.
 */
import { el } from './dom.js';
import { appendMatch } from './highlight.js';
import { computeWindow, measureRowHeight } from './virtualList.js';

const PALETTE_LIMIT = 60;
const OVERSCAN = 8;

/**
 * @param {{state: object, dom: Record<string, HTMLElement>, openFile: Function}} ctx
 */
export function createPalette(ctx) {
  const { state, dom } = ctx;
  const scroller = dom.paletteResults; // overflow-y: auto, max-height
  let returnFocus = null;
  let rows = [];
  let activeIndex = 0;
  let rowH = 0;
  let scheduled = false;
  // Search is async (it may round-trip to a worker); this token lets a slower
  // earlier query's result be discarded when a newer keystroke has superseded it.
  let renderSeq = 0;

  scroller.addEventListener('scroll', schedulePaint, { passive: true });

  function schedulePaint() {
    if (scheduled) return;
    scheduled = true;
    const run = () => {
      scheduled = false;
      paint();
    };
    if (typeof requestAnimationFrame === 'function') requestAnimationFrame(run);
    else setTimeout(run, 16);
  }

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
    const token = (renderSeq += 1);
    ctx.search.search(query, { limit: PALETTE_LIMIT }).then((results) => {
      // null = the corpus changed; stale token = a newer keystroke already ran.
      if (results === null || token !== renderSeq) return;
      rows = results;
      activeIndex = 0;
      dom.paletteEmpty.hidden = rows.length > 0;
      scroller.scrollTop = 0;
      paint();
    });
  }

  function paint() {
    if (!rowH) rowH = measureRowHeight(scroller, buildProbe);
    const total = rows.length;
    if (rowH > 0) {
      const maxScroll = Math.max(0, total * rowH - scroller.clientHeight);
      if (scroller.scrollTop > maxScroll) scroller.scrollTop = maxScroll;
    }
    const { start, end, padTop, padBottom } = computeWindow({
      scrollTop: scroller.scrollTop,
      viewportHeight: scroller.clientHeight,
      rowHeight: rowH,
      total,
      overscan: OVERSCAN,
    });
    scroller.style.paddingTop = `${padTop}px`;
    scroller.style.paddingBottom = `${padBottom}px`;
    const frag = document.createDocumentFragment();
    for (let i = start; i < end; i += 1) frag.appendChild(buildRow(rows[i], i));
    scroller.replaceChildren(frag);
  }

  function buildRow(result, index) {
    const row = el('li', 'palette-row');
    row.dataset.path = result.item;
    if (index === activeIndex) row.classList.add('active');
    appendMatch(row, result, 'pr-name', 'pr-path');
    row.addEventListener('click', () => ctx.openFile(result.item));
    return row;
  }

  function buildProbe() {
    return buildRow({ item: 'sample/file.js', target: 'sample/file.js', positions: [] }, -1);
  }

  function scrollActiveIntoView() {
    if (rowH <= 0) return;
    const top = activeIndex * rowH;
    const viewTop = scroller.scrollTop;
    const viewBottom = viewTop + scroller.clientHeight;
    if (top < viewTop) scroller.scrollTop = top;
    else if (top + rowH > viewBottom) scroller.scrollTop = top + rowH - scroller.clientHeight;
  }

  function move(delta) {
    const total = rows.length;
    if (total === 0) return;
    activeIndex = (activeIndex + delta + total) % total;
    scrollActiveIntoView();
    paint();
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
