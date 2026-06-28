/**
 * Commit history side panel for the current branch.
 */
import { el } from './dom.js';
import { commitSummary, relativeTime, shortOid } from '../format.js';

/**
 * @param {{state: object, dom: Record<string, HTMLElement>}} ctx
 */
export function createHistory(ctx) {
  const { state, store, dom } = ctx;

  function toggle() {
    store.setState({ historyOpen: !state.historyOpen });
    dom.historyPanel.hidden = !state.historyOpen;
    dom.historyBtn.setAttribute('aria-pressed', String(state.historyOpen));
    if (state.historyOpen) load();
  }

  /** Close the panel (used when switching repositories). */
  function reset() {
    store.setState({ historyOpen: false });
    dom.historyPanel.hidden = true;
    dom.historyBtn.setAttribute('aria-pressed', 'false');
  }

  async function load() {
    if (!state.source) return;
    dom.historyBranch.textContent = state.source.getCurrentBranch();
    dom.commitList.replaceChildren(el('li', 'commit-item muted', 'Loading…'));
    try {
      const commits = await state.source.log(100);
      dom.commitList.replaceChildren();
      if (commits.length === 0) {
        dom.commitList.appendChild(el('li', 'commit-item muted', 'No history.'));
        return;
      }
      for (const commit of commits) {
        const item = el('li', 'commit-item');
        item.appendChild(el('p', 'commit-msg', commitSummary(commit.message)));
        const meta = el('div', 'commit-meta');
        meta.appendChild(el('span', 'commit-oid', shortOid(commit.oid)));
        if (commit.author.name) meta.appendChild(el('span', null, commit.author.name));
        if (commit.timestamp) meta.appendChild(el('span', null, relativeTime(commit.timestamp)));
        item.appendChild(meta);
        dom.commitList.appendChild(item);
      }
    } catch (err) {
      dom.commitList.replaceChildren(el('li', 'commit-item muted', `History unavailable: ${err.message}`));
    }
  }

  return { toggle, reset, load };
}
