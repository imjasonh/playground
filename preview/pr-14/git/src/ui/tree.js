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
import { fuzzyFilter } from '../fuzzy.js';
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

  scroller.addEventListener('scroll', schedulePaint, { passive: true });
  if (typeof window !== 'undefined') {
    window.addEventListener('resize', schedulePaint, { passive: true });
  }

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
    if (query) {
      const fresh = query !== lastQuery || mode !== 'flat';
      mode = 'flat';
      dom.fileTree.hidden = true;
      dom.flatResults.hidden = false;
      flatRows = fuzzyFilter(query, state.files, { limit: FILTER_LIMIT });
      dom.treeEmpty.hidden = flatRows.length > 0;
      if (fresh) scroller.scrollTop = 0; // a new search starts at the top
      paintFlat();
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
    windowInto(dom.fileTree, treeRows, treeRowH, buildTreeRow);
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
  }

  function buildTreeRow({ node, depth }) {
    const row = el('button', 'tree-row');
    row.type = 'button';
    row.style.paddingLeft = `${0.4 + depth * 0.85}rem`;
    row.dataset.path = node.path;
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
