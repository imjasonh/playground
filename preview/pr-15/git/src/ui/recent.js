/**
 * Start-screen lists: the one-tap preset repositories and the
 * stored/recently-opened repositories backed by the registry.
 */
import { el } from './dom.js';
import { relativeTime } from '../format.js';
import { storageEstimate, describeStorage } from '../quota.js';

// One-tap sample repositories for the clone screen. Kept small (few files /
// few branches) so a shallow clone over the CORS proxy stays fast on mobile.
const PRESET_REPOS = [
  { label: 'octocat/Hello-World', url: 'https://github.com/octocat/Hello-World', note: 'Tiny GitHub sample' },
  { label: 'octocat/Spoon-Knife', url: 'https://github.com/octocat/Spoon-Knife', note: 'Classic fork demo' },
  { label: 'imjasonh/playground', url: 'https://github.com/imjasonh/playground', note: 'This repo' },
  { label: 'github/gitignore', url: 'https://github.com/github/gitignore', note: 'Lots of small files' },
];

/**
 * @param {{
 *   state: object,
 *   dom: Record<string, HTMLElement>,
 *   toast: Function,
 *   openSource: Function,
 *   startClone: Function,
 * }} ctx
 */
export function createRecent(ctx) {
  const { state, dom } = ctx;

  function renderPresets() {
    dom.presetList.replaceChildren();
    for (const preset of PRESET_REPOS) {
      const button = el('button', 'preset');
      button.type = 'button';
      button.appendChild(el('span', 'p-name', preset.label));
      if (preset.note) button.appendChild(el('span', 'p-note', preset.note));
      button.addEventListener('click', () => {
        dom.urlInput.value = preset.url;
        if (preset.ref) dom.refInput.value = preset.ref;
        ctx.startClone();
      });
      dom.presetList.appendChild(button);
    }
  }

  function renderRecent() {
    if (!state.storage) {
      dom.recent.hidden = true;
      return;
    }
    const repos = state.storage.listRepos();
    if (repos.length === 0) {
      dom.recent.hidden = true;
      return;
    }
    dom.recent.hidden = false;
    dom.recentList.replaceChildren();

    for (const repo of repos) {
      const item = el('li', 'recent-item');

      const main = el('div', 'ri-main');
      main.appendChild(el('div', 'ri-name', repo.fullName || repo.dir));
      const when = repo.lastUsed ? `opened ${relativeTime(Math.round(repo.lastUsed / 1000))}` : '';
      main.appendChild(el('div', 'ri-meta', [repo.url, when].filter(Boolean).join(' · ')));
      main.addEventListener('click', () => openStored(repo.dir));
      item.appendChild(main);

      const remove = el('button', 'ri-remove', '\u00D7');
      remove.type = 'button';
      remove.title = 'Remove from local storage';
      remove.setAttribute('aria-label', `Remove ${repo.fullName}`);
      remove.addEventListener('click', async (e) => {
        e.stopPropagation();
        try {
          await state.storage.remove(repo.dir);
          renderRecent();
          ctx.toast('Removed from local storage');
        } catch (err) {
          ctx.toast(`Could not remove: ${err.message}`, 'error');
        }
      });
      item.appendChild(remove);

      dom.recentList.appendChild(item);
    }

    renderStorageUsage();
  }

  /** Fill the IndexedDB usage meter, hiding it when the API is unavailable. */
  async function renderStorageUsage() {
    if (!dom.storageUsage) return;
    const label = describeStorage(await storageEstimate());
    dom.storageUsage.textContent = label ? `Storage: ${label}` : '';
    dom.storageUsage.hidden = !label;
  }

  async function openStored(dir) {
    try {
      ctx.toast('Opening…');
      const source = await state.storage.open(dir);
      await ctx.openSource(source);
      ctx.hideToast();
    } catch (err) {
      ctx.toast(`Could not open repository: ${err.message}`, 'error');
    }
  }

  return { renderPresets, renderRecent };
}
