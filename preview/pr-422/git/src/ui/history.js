/**
 * Commit history side panel for the current branch.
 */
import { el } from './dom.js';
import { commitSummary, relativeTime, shortOid } from '../format.js';
import { refLabel, refValue, parseRefValue } from '../repoSource.js';

/**
 * @param {{state: object, dom: Record<string, HTMLElement>}} ctx
 */
export function createHistory(ctx) {
  const { state, store, dom } = ctx;

  if (dom.compareSelect) dom.compareSelect.addEventListener('change', onCompareChange);

  function toggle() {
    const open = !state.historyOpen;
    store.setState({ historyOpen: open, historyPath: null });
    dom.historyPanel.hidden = !open;
    dom.historyBtn.setAttribute('aria-pressed', String(open));
    if (open) load();
  }

  /** Open the panel scoped to a single file's commit history. */
  function showFile(path) {
    store.setState({ historyOpen: true, historyPath: path });
    dom.historyPanel.hidden = false;
    dom.historyBtn.setAttribute('aria-pressed', 'true');
    load();
  }

  /** Drop back from file history to the current ref's history. */
  function showBranch() {
    store.setState({ historyPath: null });
    load();
  }

  /** Close the panel (used when switching repositories). */
  function reset() {
    store.setState({ historyOpen: false, historyPath: null });
    dom.historyPanel.hidden = true;
    dom.historyBtn.setAttribute('aria-pressed', 'false');
  }

  /** The current ref descriptor, tolerating sources without getCurrentRef. */
  function currentRef() {
    const source = state.source;
    if (source && typeof source.getCurrentRef === 'function') return source.getCurrentRef();
    return { type: 'branch', name: source ? source.getCurrentBranch() : '' };
  }

  function currentLabel() {
    return state.source ? refLabel(currentRef()) : '';
  }

  async function load() {
    if (!state.source) return;
    const path = state.historyPath;
    dom.historyBranch.textContent = path ? path : currentLabel();
    renderCompare();
    dom.commitList.replaceChildren(el('li', 'commit-item muted', 'Loading…'));
    try {
      const commits = path ? await loadFileLog(path) : await state.source.log(100);
      dom.commitList.replaceChildren();
      if (path) dom.commitList.appendChild(backRow());
      if (commits.length === 0) {
        dom.commitList.appendChild(
          el('li', 'commit-item muted', path ? 'No commits touched this file.' : 'No history.')
        );
        return;
      }
      for (const commit of commits) {
        dom.commitList.appendChild(commitRow(commit));
      }
    } catch (err) {
      dom.commitList.replaceChildren(el('li', 'commit-item muted', `History unavailable: ${err.message}`));
    }
  }

  function loadFileLog(path) {
    const source = state.source;
    if (typeof source.fileLog === 'function') return source.fileLog(path, 100);
    return source.log(100); // source without per-file history: show full log
  }

  /**
   * Populate the "Compare with" picker with every branch/tag except the one we
   * are already viewing. Hidden in file-history mode or when the source can't
   * diff, and whenever there's nothing else to compare against.
   */
  function renderCompare() {
    const select = dom.compareSelect;
    const wrap = dom.historyCompare;
    if (!select) return;
    const source = state.source;
    const canCompare =
      !state.historyPath && ctx.showCompare && source && typeof source.changedFiles === 'function';

    const current = currentRef();
    const options = [];
    if (canCompare) {
      for (const b of state.branches || []) {
        if (current.type === 'branch' && current.name === b.name) continue;
        options.push(['branch', b.name, `Branch: ${b.name}`]);
      }
      for (const t of state.tags || []) {
        if (current.type === 'tag' && current.name === t) continue;
        options.push(['tag', t, `Tag: ${t}`]);
      }
    }

    if (!options.length) {
      if (wrap) wrap.hidden = true;
      return;
    }
    if (wrap) wrap.hidden = false;
    select.replaceChildren();
    const placeholder = el('option', null, 'Compare with…');
    placeholder.value = '';
    select.appendChild(placeholder);
    for (const [type, name, text] of options) {
      const option = el('option', null, text);
      option.value = refValue({ type, name });
      select.appendChild(option);
    }
    select.value = '';
  }

  function onCompareChange() {
    const value = dom.compareSelect.value;
    if (!value || !ctx.showCompare) return;
    // Reset so re-selecting the same ref fires again, then diff current -> picked.
    dom.compareSelect.value = '';
    ctx.showCompare(currentRef(), parseRefValue(value));
  }

  /** A row that returns from file history to the current ref's history. */
  function backRow() {
    const li = el('li', 'commit-item history-back');
    const btn = el('button', 'commit-action', '\u2190 Back to history');
    btn.type = 'button';
    btn.addEventListener('click', showBranch);
    li.appendChild(btn);
    return li;
  }

  function commitRow(commit) {
    const item = el('li', 'commit-item');
    item.appendChild(el('p', 'commit-msg', commitSummary(commit.message)));
    const meta = el('div', 'commit-meta');
    meta.appendChild(el('span', 'commit-oid', shortOid(commit.oid)));
    if (commit.author.name) meta.appendChild(el('span', null, commit.author.name));
    if (commit.timestamp) meta.appendChild(el('span', null, relativeTime(commit.timestamp)));
    item.appendChild(meta);

    if ((ctx.browseRef || ctx.showCommitDiff) && commit.oid) {
      const actions = el('div', 'commit-actions');
      if (ctx.showCommitDiff) {
        const diff = el('button', 'commit-action', 'View changes');
        diff.type = 'button';
        diff.title = `Show files changed in ${shortOid(commit.oid)}`;
        diff.addEventListener('click', () => ctx.showCommitDiff(commit));
        actions.appendChild(diff);
      }
      if (ctx.browseRef) {
        const browse = el('button', 'commit-action', 'Browse files');
        browse.type = 'button';
        browse.title = `Browse the tree at ${shortOid(commit.oid)}`;
        browse.addEventListener('click', () => ctx.browseRef({ type: 'commit', name: commit.oid }));
        actions.appendChild(browse);
      }
      item.appendChild(actions);
    }
    return item;
  }

  return { toggle, showFile, showBranch, reset, load };
}
