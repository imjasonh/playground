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

  await page.selectOption('#branch-select', 'feature/dark-mode');
  await expect(page.locator('#repo-meta')).toContainText('feature/dark-mode');

  await page.locator('#tree-filter').fill('theme.js');
  await expect(page.locator('.flat-row', { hasText: 'theme.js' })).toBeVisible();
});

test('shows commit history for the current branch', async ({ page }) => {
  await loadDemo(page);
  await page.getByRole('button', { name: 'History' }).click();
  await expect(page.locator('#history-panel')).toBeVisible();
  await expect(page.locator('#history-branch')).toHaveText('main');
  await expect(page.locator('.commit-item').first()).toBeVisible();
});

test('Pull / Update reports that demo data is static', async ({ page }) => {
  await loadDemo(page);
  await page.getByRole('button', { name: 'Pull / Update' }).click();
  await expect(page.locator('#toast')).toContainText(/static/i);
});

test('exposes ARIA tree semantics for the file list', async ({ page }) => {
  await loadDemo(page);
  await expect(page.locator('#file-tree')).toHaveAttribute('role', 'tree');
  await expect(page.locator('.tree-row[role="treeitem"]').first()).toBeVisible();
  // Directories advertise their expanded state to assistive tech.
  await expect(page.locator('.tree-row[aria-expanded]').first()).toBeVisible();
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
