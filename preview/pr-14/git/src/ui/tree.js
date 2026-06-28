/**
 * Sidebar: the collapsible file tree and the flat fuzzy-filter results that
 * replace it while the filter box has a query.
 *
 * Both lists are virtualized — only the rows near the viewport are built as DOM
 * nodes, while top/bottom padding keeps the scrollbar sized for the whole list
 * — so a repo with tens of thousands of files stays responsive. Windowing is
 * transparent below the viewport size: when the list isn't laid out yet (or is
 * smaller than the viewport) every row is rendered, so nothing is ever hidden.
 */
import { el } from './dom.js';
import { appendMatch } from './highlight.js';
import { flattenVisible } from '../fileTree.js';
import { computeWindow, measureRowHeight } from './virtualList.js';

const FILTER_LIMIT = 400;
const OVERSCAN = 8;

/**
 * @param {{state: object, dom: Record<string, HTMLElement>, openFile: Function}} ctx
 */
export function createTree(ctx) {
  const { state, store, dom } = ctx;
  const scroller = dom.fileTree.parentElement; // .tree-scroll (the scroll box)

  let mode = 'tree'; // 'tree' | 'flat'
  let treeRows = [];
  let flatRows = [];
  let treeRowH = 0;
  let flatRowH = 0;
  let lastQuery = '';
  let scheduled = false;
  // Roving-tabindex cursor into treeRows for keyboard navigation.
  let focusIndex = 0;
  // Filtering is async (it may round-trip to a worker); bumped on every
  // renderSidebar so a slower flat-search result for a superseded query (or one
  // that arrives after the filter was cleared) is discarded.
  let renderSeq = 0;

  scroller.addEventListener('scroll', schedulePaint, { passive: true });
  if (typeof window !== 'undefined') {
    window.addEventListener('resize', schedulePaint, { passive: true });
  }
  dom.fileTree.addEventListener('keydown', onTreeKey);

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

  function paint() {
    if (mode === 'flat') paintFlat();
    else paintTree();
  }

  /** Render either the tree or the flat filter results for the current query. */
  function renderSidebar() {
    const query = dom.treeFilter.value.trim();
    const token = (renderSeq += 1);
    if (query) {
      const fresh = query !== lastQuery || mode !== 'flat';
      mode = 'flat';
      dom.fileTree.hidden = true;
      dom.flatResults.hidden = false;
      ctx.search.search(query, { limit: FILTER_LIMIT }).then((results) => {
        // null = corpus changed; stale token = a newer render (incl. clearing
        // the filter back to the tree) has superseded this search.
        if (results === null || token !== renderSeq) return;
        flatRows = results;
        dom.treeEmpty.hidden = flatRows.length > 0;
        if (fresh) scroller.scrollTop = 0; // a new search starts at the top
        paintFlat();
      });
    } else {
      const leftSearch = mode !== 'tree';
      mode = 'tree';
      dom.flatResults.hidden = true;
      dom.fileTree.hidden = false;
      treeRows = flattenVisible(state.tree, state.expanded);
      dom.treeEmpty.hidden = treeRows.length > 0;
      if (leftSearch) scroller.scrollTop = 0;
      paintTree();
    }
    lastQuery = query;
  }

  function paintTree() {
    if (!treeRowH) treeRowH = measureRowHeight(dom.fileTree, buildTreeProbe);
    if (focusIndex > treeRows.length - 1) focusIndex = Math.max(0, treeRows.length - 1);
    windowInto(dom.fileTree, treeRows, treeRowH, buildTreeRow);
    ensureTabbable();
  }

  /** Keep one row in the tab order even when focusIndex is scrolled offscreen. */
  function ensureTabbable() {
    if (mode !== 'tree') return;
    if (dom.fileTree.querySelector('.tree-row[tabindex="0"]')) return;
    const first = dom.fileTree.querySelector('.tree-row');
    if (first) first.tabIndex = 0;
  }

  function paintFlat() {
    if (!flatRowH) flatRowH = measureRowHeight(dom.flatResults, buildFlatProbe);
    windowInto(dom.flatResults, flatRows, flatRowH, buildFlatRow);
  }

  /** Render only the windowed slice of `rows` into `list`, padding the rest. */
  function windowInto(list, rows, rowHeight, build) {
    const total = rows.length;
    // Clamp a stale scroll position (e.g. after switching to a smaller branch)
    // so we never strand the viewport past the end showing a blank window.
    if (rowHeight > 0) {
      const maxScroll = Math.max(0, total * rowHeight - scroller.clientHeight);
      if (scroller.scrollTop > maxScroll) scroller.scrollTop = maxScroll;
    }
    const { start, end, padTop, padBottom } = computeWindow({
      scrollTop: scroller.scrollTop,
      viewportHeight: scroller.clientHeight,
      rowHeight,
      total,
      overscan: OVERSCAN,
    });
    list.style.paddingTop = `${padTop}px`;
    list.style.paddingBottom = `${padBottom}px`;
    const frag = document.createDocumentFragment();
    for (let i = start; i < end; i += 1) frag.appendChild(build(rows[i], i));
    list.replaceChildren(frag);
  }

  /** Reset the sidebar scroll position (called when opening a new repository). */
  function resetScroll() {
    scroller.scrollTop = 0;
    focusIndex = 0;
  }

  function buildTreeRow({ node, depth }, index = -1) {
    const row = el('button', 'tree-row');
    row.type = 'button';
    row.style.paddingLeft = `${0.4 + depth * 0.85}rem`;
    row.dataset.path = node.path;
    row.dataset.index = String(index);
    // Roving tabindex: only the focused row is in the tab order.
    row.tabIndex = index === focusIndex ? 0 : -1;
    row.setAttribute('role', 'treeitem');
    row.setAttribute('aria-level', String(depth + 1));

    const twisty = el('span', 'twisty');
    twisty.setAttribute('aria-hidden', 'true');
    if (node.type === 'dir') {
      twisty.textContent = '\u203A'; // ›
      const open = state.expanded.has(node.path);
      if (open) row.classList.add('open');
      row.setAttribute('aria-expanded', String(open));
    } else {
      twisty.textContent = '';
    }
    row.appendChild(twisty);

    const icon = el('span', 'node-icon', node.type === 'dir' ? '\u{1F4C1}' : '\u{1F4C4}');
    icon.setAttribute('aria-hidden', 'true');
    row.appendChild(icon);
    row.appendChild(el('span', 'node-name', node.name));

    if (node.type === 'file' && node.path === state.activePath) {
      row.classList.add('active');
      row.setAttribute('aria-current', 'true');
    }

    row.addEventListener('click', () => {
      if (index >= 0) focusIndex = index; // keep keyboard cursor in sync
      if (node.type === 'dir') {
        toggleDir(node.path);
      } else {
        ctx.openFile(node.path);
      }
    });
    return row;
  }

  function buildTreeProbe() {
    return buildTreeRow({
      node: { name: 'sample', path: 'sample', type: 'file', children: [] },
      depth: 0,
    });
  }

  function toggleDir(path) {
    store.update((s) => {
      if (s.expanded.has(path)) s.expanded.delete(path);
      else s.expanded.add(path);
    });
    treeRows = flattenVisible(state.tree, state.expanded);
    paintTree();
  }

  /* ---------------------------------------------------------------- */
  /* Keyboard navigation (WAI-ARIA tree pattern)                       */
  /* ---------------------------------------------------------------- */

  function onTreeKey(event) {
    if (mode !== 'tree' || treeRows.length === 0) return;
    // Trust the actually-focused row (handles Tab / click / programmatic focus).
    const active = document.activeElement;
    const activeIdx = active && active.dataset ? Number(active.dataset.index) : NaN;
    if (Number.isInteger(activeIdx) && activeIdx >= 0) focusIndex = activeIdx;
    const current = treeRows[focusIndex];
    if (!current) return;
    const { node, depth } = current;
    const expanded = node.type === 'dir' && state.expanded.has(node.path);

    switch (event.key) {
      case 'ArrowDown':
        event.preventDefault();
        moveFocus(focusIndex + 1);
        break;
      case 'ArrowUp':
        event.preventDefault();
        moveFocus(focusIndex - 1);
        break;
      case 'Home':
        event.preventDefault();
        moveFocus(0);
        break;
      case 'End':
        event.preventDefault();
        moveFocus(treeRows.length - 1);
        break;
      case 'ArrowRight':
        event.preventDefault();
        if (node.type === 'dir' && !expanded) toggleFocusedDir(node.path);
        else if (expanded) moveFocus(focusIndex + 1); // descend to first child
        break;
      case 'ArrowLeft':
        event.preventDefault();
        if (expanded) toggleFocusedDir(node.path);
        else moveFocus(parentIndex(focusIndex, depth));
        break;
      case 'Enter':
      case ' ':
        event.preventDefault();
        if (node.type === 'dir') toggleFocusedDir(node.path);
        else ctx.openFile(node.path);
        break;
      default:
        break;
    }
  }

  function moveFocus(next) {
    const clamped = Math.max(0, Math.min(next, treeRows.length - 1));
    focusIndex = clamped;
    ensureVisible(clamped);
    paintTree();
    focusRow(clamped);
  }

  /** Expand/collapse the focused dir, keeping focus on it after the repaint. */
  function toggleFocusedDir(path) {
    toggleDir(path);
    focusRow(focusIndex);
  }

  function focusRow(index) {
    const node = dom.fileTree.querySelector(`.tree-row[data-index="${index}"]`);
    // We've already scrolled it into view; preventScroll avoids a double jump.
    if (node) node.focus({ preventScroll: true });
  }

  /** Scroll so row `index` is within the viewport before it's painted/focused. */
  function ensureVisible(index) {
    if (!treeRowH) return;
    const top = index * treeRowH;
    const bottom = top + treeRowH;
    if (top < scroller.scrollTop) scroller.scrollTop = top;
    else if (bottom > scroller.scrollTop + scroller.clientHeight) {
      scroller.scrollTop = bottom - scroller.clientHeight;
    }
  }

  /**
   * Index of the nearest preceding row one level shallower (the parent dir), or
   * the row itself when it's already at the top level (so focus stays put).
   */
  function parentIndex(index, depth) {
    for (let i = index - 1; i >= 0; i -= 1) {
      if (treeRows[i].depth === depth - 1) return i;
    }
    return index; // already at top level: stay put
  }

  function buildFlatRow(result) {
    const row = el('li', 'flat-row');
    row.dataset.path = result.item;
    row.setAttribute('role', 'option');
    if (result.item === state.activePath) {
      row.classList.add('active');
      row.setAttribute('aria-selected', 'true');
    }
    appendMatch(row, result, 'fr-name', 'fr-path');
    row.addEventListener('click', () => ctx.openFile(result.item));
    return row;
  }

  function buildFlatProbe() {
    return buildFlatRow({ item: 'sample/file.js', target: 'sample/file.js', positions: [] });
  }

  return { renderSidebar, resetScroll };
}
