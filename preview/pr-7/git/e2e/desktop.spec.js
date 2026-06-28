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

// ---------------------------------------------------------------------------
// Read-write flow (edit / create / delete -> stage -> commit). The demo repo
// is editable but has no remote, so this exercises everything except push.
// ---------------------------------------------------------------------------

test('exposes editing affordances but hides push for the demo repo', async ({ page }) => {
  await loadDemo(page);
  await expect(page.locator('#changes-btn')).toBeVisible();
  await expect(page.locator('#new-file-btn')).toBeVisible();

  await page.locator('#changes-btn').click();
  await expect(page.locator('#changes-panel')).toBeVisible();
  // The in-memory demo has no remote, so the push controls stay hidden.
  await expect(page.locator('#push-section')).toBeHidden();
});

test('edits a file, stages it, and commits', async ({ page }) => {
  await loadDemo(page);
  await page.locator('.tree-row', { hasText: 'README.md' }).click();
  await expect(page.locator('#edit-btn')).toBeVisible();

  await page.locator('#edit-btn').click();
  const area = page.locator('.editor-area');
  await expect(area).toBeVisible();
  await area.fill('# Edited by the e2e test\n');
  await page.getByRole('button', { name: 'Save', exact: true }).click();

  // The viewer reflects the staged edit and the badge counts one change.
  await expect(page.locator('.code-view .code')).toContainText('Edited by the e2e test');
  await expect(page.locator('#changes-count')).toHaveText('1');

  await page.locator('#changes-btn').click();
  await expect(page.locator('.change-item.modified', { hasText: 'README.md' })).toBeVisible();

  await page.locator('#author-name').fill('Tester');
  await page.locator('#author-email').fill('tester@example.com');
  await page.locator('#commit-message').fill('Edit README in e2e');
  await page.locator('#commit-btn').click();

  await expect(page.locator('#toast')).toContainText(/Committed/);
  await expect(page.locator('#changes-empty')).toBeVisible();
  await expect(page.locator('#changes-count')).toBeHidden();

  // The new commit tops the history.
  await page.locator('#history-btn').click();
  await expect(page.locator('.commit-item').first()).toContainText('Edit README in e2e');
});

test('creates a new file through the modal and stages it', async ({ page }) => {
  await loadDemo(page);
  await page.locator('#new-file-btn').click();
  await expect(page.locator('#newfile-overlay')).toBeVisible();

  await page.locator('#newfile-input').fill('notes/todo.md');
  await page.locator('#newfile-create').click();

  const area = page.locator('.editor-area');
  await expect(area).toBeVisible();
  await area.fill('- write more tests\n');
  await page.getByRole('button', { name: 'Save', exact: true }).click();

  await expect(page.locator('#changes-count')).toHaveText('1');
  await page.locator('#tree-filter').fill('todo.md');
  await expect(page.locator('.flat-row', { hasText: 'todo.md' })).toBeVisible();
});

test('rejects a duplicate path in the new-file modal', async ({ page }) => {
  await loadDemo(page);
  await page.locator('#new-file-btn').click();
  await page.locator('#newfile-input').fill('README.md');
  await page.locator('#newfile-create').click();
  await expect(page.locator('#newfile-error')).toBeVisible();
  await expect(page.locator('#newfile-overlay')).toBeVisible();
});

test('deletes a file and stages the removal', async ({ page }) => {
  await loadDemo(page);
  await page.locator('.tree-row', { hasText: 'README.md' }).click();

  page.once('dialog', (dialog) => dialog.accept());
  await page.locator('#delete-btn').click();

  await expect(page.locator('#changes-count')).toHaveText('1');
  await page.locator('#changes-btn').click();
  await expect(page.locator('.change-item.deleted', { hasText: 'README.md' })).toBeVisible();
});
