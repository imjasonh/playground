import { test, expect } from '@playwright/test';

// All desktop tests run against the built-in demo repository, so they exercise
// the real code-browser UI (tree, viewer, fuzzy finder, branch switching,
// history) without any network access.

async function loadDemo(page) {
  await page.goto('/');
  await page.getByRole('button', { name: 'Try a demo (no network)' }).click();
  await expect(page.locator('#repo-bar')).toBeVisible();
  await expect(page.locator('#browser-view')).toBeVisible();
}

test('offers one-tap preset repositories on the start screen', async ({ page }) => {
  await page.goto('/');
  await expect(page.locator('.preset')).toHaveCount(4);
  await expect(page.locator('.preset', { hasText: 'octocat/Hello-World' })).toBeVisible();

  // Clicking a preset fills the URL field (we don't assert the network clone).
  await page.locator('.preset', { hasText: 'github/gitignore' }).click();
  await expect(page.locator('#url-input')).toHaveValue('https://github.com/github/gitignore');
});

test('loads the demo repo and shows the file tree and branches', async ({ page }) => {
  await loadDemo(page);
  await expect(page.locator('#repo-name')).toHaveText('tasklite/demo');
  await expect(page.locator('.tree-row', { hasText: 'README.md' })).toBeVisible();
  await expect(page.locator('.tree-row', { hasText: 'src' })).toBeVisible();

  const branches = await page.locator('#branch-select option').allTextContents();
  expect(branches).toContain('main');
  expect(branches).toContain('feature/dark-mode');
});

test('opens a file and renders contents with line numbers', async ({ page }) => {
  await loadDemo(page);
  await page.locator('.tree-row', { hasText: 'README.md' }).click();

  await expect(page.locator('#viewer-head')).toBeVisible();
  await expect(page.locator('#file-path')).toContainText('README.md');
  await expect(page.locator('.code-view .code')).toContainText('Tasklite');
  await expect(page.locator('.code-view .gutter')).toContainText('1');
  await expect(page.locator('#file-info')).toContainText(/lines/);
});

test('syntax-highlights source files in the viewer', async ({ page }) => {
  await loadDemo(page);
  await page.locator('#tree-filter').fill('storage.js');
  await page.locator('.flat-row', { hasText: 'storage.js' }).click();
  await expect(page.locator('#file-path')).toContainText('storage.js');

  // Tokens render as colored spans; a JS file should have keywords and strings.
  await expect(page.locator('.code .tok-keyword').first()).toBeVisible();
  await expect(page.locator('.code .tok-string').first()).toBeVisible();
  // The full text is still intact despite the wrapping spans.
  await expect(page.locator('.code')).toContainText('export function loadTasks');
});

test('finds files with the command palette', async ({ page }) => {
  await loadDemo(page);
  await page.getByRole('button', { name: 'Find files' }).click();
  await expect(page.locator('#palette')).toBeVisible();

  await page.locator('#palette-input').fill('render');
  await expect(page.locator('.palette-row').first()).toContainText('render.js');

  await page.locator('#palette-input').press('Enter');
  await expect(page.locator('#palette')).toBeHidden();
  await expect(page.locator('#file-path')).toContainText('render.js');
});

test('runs fuzzy file search in a Web Worker', async ({ page }) => {
  await loadDemo(page);

  // The worker is the active backend in a modern browser (it falls back to
  // synchronous search only where Workers are unavailable).
  await expect
    .poll(() => page.evaluate(() => window.gitBrowser?.search?.usingWorker))
    .toBe(true);

  // Worker-backed tree filtering still returns ranked matches.
  await page.locator('#tree-filter').fill('render');
  await expect(page.locator('.flat-row').first()).toContainText('render.js');

  // …and so does the palette, sharing the same worker.
  await page.getByRole('button', { name: 'Find files' }).click();
  await page.locator('#palette-input').fill('storage');
  await expect(page.locator('.palette-row').first()).toContainText('storage.js');
});

test('searches file contents in a Web Worker and opens a match at its line', async ({ page }) => {
  await loadDemo(page);

  await expect
    .poll(() => page.evaluate(() => window.gitBrowser?.contentSearch?.usingWorker))
    .toBe(true);

  await page.getByRole('button', { name: 'Search code' }).click();
  await expect(page.locator('#content-search')).toBeVisible();

  await page.locator('#content-search-input').fill('loadTasks');
  // Results stream in grouped by file, with the matched text highlighted.
  await expect(page.locator('.cs-file', { hasText: 'src/storage.js' })).toBeVisible();
  await expect(page.locator('.cs-hit').first()).toBeVisible();
  await expect(page.locator('#content-search-status')).toContainText(/match/);

  // Clicking a match opens the file at that line and deep-links it.
  await page
    .locator('.cs-file', { hasText: 'src/storage.js' })
    .locator('.cs-line')
    .first()
    .click();
  await expect(page.locator('#content-search')).toBeHidden();
  await expect(page.locator('#file-path')).toContainText('storage.js');
  await expect(page.locator('.line-highlight')).toBeVisible();
  await expect.poll(() => page.evaluate(() => location.hash)).toContain('file=src/storage.js');
});

test('content search supports regex and reports an empty result', async ({ page }) => {
  await loadDemo(page);
  await page.keyboard.press('Control+Shift+F');
  await expect(page.locator('#content-search')).toBeVisible();

  await page.locator('#cs-regex').check();
  await page.locator('#content-search-input').fill('export\\s+function');
  await expect(page.locator('.cs-line').first()).toBeVisible();

  await page.locator('#content-search-input').fill('zzz_no_such_text_zzz');
  await expect(page.locator('#content-search-empty')).toBeVisible();
});

test('Ctrl/Cmd+P toggles the palette', async ({ page }) => {
  await loadDemo(page);
  await page.keyboard.press('Control+p');
  await expect(page.locator('#palette')).toBeVisible();
  await page.keyboard.press('Escape');
  await expect(page.locator('#palette')).toBeHidden();
});

test('renders an SVG image file as an image', async ({ page }) => {
  await loadDemo(page);
  await page.locator('#tree-filter').fill('logo.svg');
  await page.locator('.flat-row', { hasText: 'logo.svg' }).click();
  await expect(page.locator('.image-view img')).toBeVisible();
  await expect(page.locator('#file-info')).toContainText(/Image/);
});

test('switching branches changes the available files', async ({ page }) => {
  await loadDemo(page);

  // theme.js exists only on feature/dark-mode
  await page.locator('#tree-filter').fill('theme.js');
  await expect(page.locator('#tree-empty')).toBeVisible();

  await page.selectOption('#branch-select', { label: 'feature/dark-mode' });
  await expect(page.locator('#repo-meta')).toContainText('feature/dark-mode');

  await page.locator('#tree-filter').fill('theme.js');
  await expect(page.locator('.flat-row', { hasText: 'theme.js' })).toBeVisible();
});

test('lists tags in the ref picker and can browse one', async ({ page }) => {
  await loadDemo(page);
  // Branches and Tags are grouped in the picker.
  await expect(page.locator('#branch-select optgroup[label="Branches"]')).toHaveCount(1);
  await expect(page.locator('#branch-select optgroup[label="Tags"]')).toHaveCount(1);

  await page.selectOption('#branch-select', 'tag:v0.3.0');
  await expect(page.locator('#repo-meta')).toContainText('v0.3.0');
  await expect(page.locator('#toast')).toContainText(/Switched to v0\.3\.0/);
});

test('browses the tree at a commit from history', async ({ page }) => {
  await loadDemo(page);
  await page.getByRole('button', { name: 'History' }).click();
  await expect(page.locator('#history-panel')).toBeVisible();

  await page
    .locator('.commit-item')
    .first()
    .getByRole('button', { name: 'Browse files' })
    .click();
  // The picker now reflects a detached "Viewing" entry and the tree still loads.
  await expect(page.locator('#branch-select optgroup[label="Viewing"]')).toHaveCount(1);
  await expect(page.locator('.tree-row', { hasText: 'README.md' })).toBeVisible();
});

test('shows commit history for the current branch', async ({ page }) => {
  await loadDemo(page);
  await page.getByRole('button', { name: 'History' }).click();
  await expect(page.locator('#history-panel')).toBeVisible();
  await expect(page.locator('#history-branch')).toHaveText('main');
  await expect(page.locator('.commit-item').first()).toBeVisible();
});

test('shows file-scoped history from the viewer header', async ({ page }) => {
  await loadDemo(page);
  await page.locator('.tree-row', { hasText: 'README.md' }).click();
  await expect(page.locator('#file-path')).toContainText('README.md');

  await page.locator('#file-history-btn').click();
  await expect(page.locator('#history-panel')).toBeVisible();
  await expect(page.locator('#history-branch')).toHaveText('README.md');
  // Per the demo annotations, README.md only changed in the initial commit.
  await expect(page.locator('.commit-item .commit-msg')).toHaveCount(1);
  await expect(page.locator('.commit-item', { hasText: 'Initial commit' })).toBeVisible();

  // The back affordance returns to the ref's full history.
  await page.locator('.history-back .commit-action').click();
  await expect(page.locator('#history-branch')).toHaveText('main');
  await expect(page.locator('.commit-item .commit-msg').first()).toBeVisible();
});

test('compares the current ref with another from the history panel', async ({ page }) => {
  await loadDemo(page);
  await page.getByRole('button', { name: 'History' }).click();
  await expect(page.locator('#history-panel')).toBeVisible();

  // Compare main -> feature/dark-mode via the "Compare with" picker.
  await page.selectOption('#compare-select', 'branch:feature/dark-mode');

  // The viewer switches to a changed-files summary (3 files differ).
  await expect(page.locator('#file-path')).toContainText('Compare');
  await expect(page.locator('.diff-file')).toHaveCount(3);
  // theme.js exists only on the dark-mode branch, so it reads as added.
  await expect(
    page.locator('.diff-file', { hasText: 'src/theme.js' }).locator('.diff-badge')
  ).toHaveText('A');

  // Expanding a modified file lazily reveals its per-line diff.
  await page
    .locator('.diff-file', { hasText: 'src/app.js' })
    .locator('.diff-file-head')
    .click();
  await expect(
    page.locator('.diff-file', { hasText: 'src/app.js' }).locator('.diff-row.add').first()
  ).toBeVisible();
});

test("shows a commit's changed files from history", async ({ page }) => {
  await loadDemo(page);
  await page.getByRole('button', { name: 'History' }).click();
  await expect(page.locator('#history-panel')).toBeVisible();

  // The initial commit has no parent, so every file reads as an addition.
  await page
    .locator('.commit-item', { hasText: 'Initial commit' })
    .getByRole('button', { name: 'View changes' })
    .click();

  await expect(page.locator('#file-path')).toContainText('Changes in');
  await expect(page.locator('.diff-file').first()).toBeVisible();
  await expect(
    page.locator('.diff-file', { hasText: 'README.md' }).locator('.diff-badge')
  ).toHaveText('A');
});

test('disables Pull / Update for a source with no remote (demo)', async ({ page }) => {
  await loadDemo(page);
  // The demo source advertises no fetch capability, so the affordance is
  // disabled rather than offering an action that can't do anything.
  const update = page.getByRole('button', { name: 'Pull / Update' });
  await expect(update).toBeDisabled();
  await expect(update).toHaveAttribute('title', /no remote/i);
});

test('exposes ARIA tree semantics for the file list', async ({ page }) => {
  await loadDemo(page);
  await expect(page.locator('#file-tree')).toHaveAttribute('role', 'tree');
  await expect(page.locator('.tree-row[role="treeitem"]').first()).toBeVisible();
  // Directories advertise their expanded state to assistive tech.
  await expect(page.locator('.tree-row[aria-expanded]').first()).toBeVisible();
});

test('navigates the file tree with the keyboard', async ({ page }) => {
  await loadDemo(page);
  const rows = page.locator('#file-tree .tree-row');

  // Arrow keys move a roving focus through the rows.
  await rows.first().focus();
  await expect(rows.first()).toBeFocused();
  await page.keyboard.press('ArrowDown');
  await expect(rows.nth(1)).toBeFocused();
  await page.keyboard.press('ArrowUp');
  await expect(rows.first()).toBeFocused();

  // ArrowRight expands a directory; a child row appears; ArrowLeft collapses it.
  const srcDir = page.locator('#file-tree .tree-row', { hasText: 'src' }).first();
  await srcDir.focus();
  await page.keyboard.press('ArrowRight');
  await expect(srcDir).toHaveAttribute('aria-expanded', 'true');
  await expect(page.locator('#file-tree .tree-row', { hasText: 'storage.js' })).toBeVisible();

  await page.keyboard.press('ArrowLeft');
  await expect(srcDir).toHaveAttribute('aria-expanded', 'false');
  await expect(page.locator('#file-tree .tree-row', { hasText: 'storage.js' })).toHaveCount(0);

  // Enter on a file opens it in the viewer.
  const readme = page.locator('#file-tree .tree-row', { hasText: 'README.md' });
  await readme.focus();
  await page.keyboard.press('Enter');
  await expect(page.locator('#file-path')).toContainText('README.md');
});

test('returns focus to the trigger when the palette closes', async ({ page }) => {
  await loadDemo(page);
  await page.getByRole('button', { name: 'Find files' }).click();
  await expect(page.locator('#palette')).toBeVisible();

  await page.locator('#palette-input').press('Escape');
  await expect(page.locator('#palette')).toBeHidden();
  await expect(page.getByRole('button', { name: 'Find files' })).toBeFocused();
});

/* ------------------------------------------------------------------ */
/* Deep-linkable state (repo + ref + file + lines in the URL hash)     */
/* ------------------------------------------------------------------ */

test('encodes the open file and selected lines in the URL hash', async ({ page }) => {
  await loadDemo(page);
  await page.locator('.tree-row', { hasText: 'README.md' }).click();
  await expect(page.locator('#file-path')).toContainText('README.md');
  await expect(page).toHaveURL(/file=README\.md/);

  // Clicking a line number selects it, highlights it, and records it in the URL.
  await page.locator('.code-view .gutter').click({ position: { x: 6, y: 6 } });
  await expect(page.locator('.code-view .line-highlight')).toBeVisible();
  await expect(page).toHaveURL(/lines=1/);
});

test('reflects the current ref in the hash when switching branches', async ({ page }) => {
  await loadDemo(page);
  await page.selectOption('#branch-select', { label: 'feature/dark-mode' });
  await expect(page.locator('#repo-meta')).toContainText('feature/dark-mode');
  await expect(page).toHaveURL(/ref=branch:feature\/dark-mode/);
});

test('restores a deep-linked file and line range on load', async ({ page }) => {
  await page.goto('/#repo=demo&ref=branch:main&file=src/storage.js&lines=2-4');
  // The demo repo opens, the linked file is shown, and the lines are highlighted.
  await expect(page.locator('#browser-view')).toBeVisible();
  await expect(page.locator('#file-path')).toContainText('storage.js');
  await expect(page.locator('.code-view .line-highlight')).toBeVisible();
  // The deep link survives the round-trip.
  await expect(page).toHaveURL(/file=src\/storage\.js/);
  await expect(page).toHaveURL(/lines=2-4/);
});

test('restores a deep-linked non-default branch on load', async ({ page }) => {
  await page.goto('/#repo=demo&ref=branch:feature/dark-mode&file=src/theme.js');
  await expect(page.locator('#browser-view')).toBeVisible();
  await expect(page.locator('#repo-meta')).toContainText('feature/dark-mode');
  await expect(page.locator('#file-path')).toContainText('theme.js');
  await expect(page.locator('.code-view .code')).toContainText('initTheme');
});

/* ------------------------------------------------------------------ */
/* Virtualized large repository (windowed tree / filter / palette)     */
/* ------------------------------------------------------------------ */

// Inject a synthetic 5,000-file RepoSource through the same public hook the
// app exposes, so we can exercise the windowing without any network/clone.
async function loadLargeRepo(page, fileCount = 5000) {
  await page.goto('/');
  await page.waitForFunction(() => !!(window.gitBrowser && window.gitBrowser.openSource));
  await page.evaluate((n) => {
    const files = [];
    for (let i = 0; i < n; i += 1) files.push(`file${String(i).padStart(4, '0')}.txt`);
    const enc = new TextEncoder();
    window.gitBrowser.openSource({
      fullName: 'big/repo',
      url: null,
      readOnly: true,
      getCurrentBranch: () => 'main',
      listBranches: async () => [{ name: 'main', current: true }],
      setBranch: async () => {},
      listFiles: async () => files,
      readFile: async (p) => enc.encode(`contents of ${p}\n`),
      headCommit: async () => null,
      log: async () => [],
      update: async () => ({ updated: false, changed: false }),
    });
  }, fileCount);
  await expect(page.locator('#browser-view')).toBeVisible();
  await expect(page.locator('#repo-meta')).toContainText('5000 files');
}

test('virtualizes the tree for a large repository', async ({ page }) => {
  await loadLargeRepo(page);
  await expect(page.locator('.tree-row').first()).toBeVisible();

  // Only a windowed slice is in the DOM, not all 5,000 rows.
  const rendered = await page.locator('.tree-row').count();
  expect(rendered).toBeGreaterThan(0);
  expect(rendered).toBeLessThan(200);

  await expect(page.locator('.tree-row', { hasText: 'file0000.txt' })).toBeVisible();
  await expect(page.locator('.tree-row', { hasText: 'file4999.txt' })).toHaveCount(0);
});

test('scrolling the tree reveals later rows', async ({ page }) => {
  await loadLargeRepo(page);
  await page.locator('.tree-scroll').evaluate((el) => {
    el.scrollTop = el.scrollHeight;
  });
  await expect(page.locator('.tree-row', { hasText: 'file4999.txt' })).toBeVisible();
  expect(await page.locator('.tree-row').count()).toBeLessThan(200);
});

test('virtualizes the flat filter results', async ({ page }) => {
  await loadLargeRepo(page);
  await page.locator('#tree-filter').fill('file');
  await expect(page.locator('.flat-row').first()).toBeVisible();

  const rendered = await page.locator('.flat-row').count();
  expect(rendered).toBeGreaterThan(0);
  expect(rendered).toBeLessThan(200);
});

test('palette keyboard navigation works with a windowed list', async ({ page }) => {
  await loadLargeRepo(page);
  await page.getByRole('button', { name: 'Find files' }).click();
  await expect(page.locator('#palette')).toBeVisible();

  await page.locator('#palette-input').fill('file');
  await expect(page.locator('.palette-row').first()).toBeVisible();
  const rendered = await page.locator('.palette-row').count();
  expect(rendered).toBeGreaterThan(0);
  expect(rendered).toBeLessThan(60);

  await page.locator('#palette-input').press('ArrowDown');
  await page.locator('#palette-input').press('ArrowDown');
  await page.locator('#palette-input').press('Enter');
  await expect(page.locator('#palette')).toBeHidden();
  await expect(page.locator('#file-path')).toContainText('.txt');
});
