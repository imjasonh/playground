/**
 * Sidebar: the collapsible file tree and the flat fuzzy-filter results that
 * replace it while the filter box has a query.
 */
import { el } from './dom.js';
import { appendMatch } from './highlight.js';
import { flattenVisible } from '../fileTree.js';
import { fuzzyFilter } from '../fuzzy.js';

const FILTER_LIMIT = 400;

/**
 * @param {{state: object, dom: Record<string, HTMLElement>, openFile: Function}} ctx
 */
export function createTree(ctx) {
  const { state, dom } = ctx;

  /** Render either the tree or the flat filter results for the current query. */
  function renderSidebar() {
    const query = dom.treeFilter.value.trim();
    if (query) {
      renderFlatResults(query);
    } else {
      dom.flatResults.hidden = true;
      dom.fileTree.hidden = false;
      renderTree();
    }
  }

  function renderTree() {
    const rows = flattenVisible(state.tree, state.expanded);
    const list = dom.fileTree;
    list.replaceChildren();
    dom.treeEmpty.hidden = rows.length > 0;

    for (const { node, depth } of rows) {
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

      if (node.type === 'file' && state.changedPaths && state.changedPaths.has(node.path)) {
        row.classList.add('changed');
        const dot = el('span', 'change-dot');
        dot.setAttribute('aria-hidden', 'true');
        dot.title = 'Uncommitted change';
        row.appendChild(dot);
      }

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
      list.appendChild(row);
    }
  }

  function toggleDir(path) {
    if (state.expanded.has(path)) state.expanded.delete(path);
    else state.expanded.add(path);
    renderTree();
  }

  function renderFlatResults(query) {
    dom.fileTree.hidden = true;
    const list = dom.flatResults;
    list.hidden = false;
    list.replaceChildren();

    const results = fuzzyFilter(query, state.files, { limit: FILTER_LIMIT });
    dom.treeEmpty.hidden = results.length > 0;

    for (const result of results) {
      const row = el('li', 'flat-row');
      row.dataset.path = result.item;
      row.setAttribute('role', 'option');
      if (state.changedPaths && state.changedPaths.has(result.item)) row.classList.add('changed');
      if (result.item === state.activePath) {
        row.classList.add('active');
        row.setAttribute('aria-selected', 'true');
      }
      appendMatch(row, result, 'fr-name', 'fr-path');
      row.addEventListener('click', () => ctx.openFile(result.item));
      list.appendChild(row);
    }
  }

  return { renderSidebar, renderTree };
}
