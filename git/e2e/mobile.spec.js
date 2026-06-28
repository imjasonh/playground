import { test, expect } from '@playwright/test';

// Mobile tests use the #demo deep link to auto-load the demo repo.

test.beforeEach(async ({ page }) => {
  await page.goto('/#demo');
  await expect(page.locator('#browser-view')).toBeVisible();
});

test('header stays compact when a repo is open', async ({ page }) => {
  // The "git" brand is hidden on mobile while browsing, and the action row
  // scrolls horizontally instead of wrapping into a tall block.
  await expect(page.locator('.topbar .brand')).toBeHidden();
  const topbar = await page.locator('.topbar').boundingBox();
  expect(topbar).not.toBeNull();
  expect(topbar.height).toBeLessThan(140);
});

test('demo loads on mobile and the sidebar spans the width', async ({ page }) => {
  const box = await page.locator('.sidebar').boundingBox();
  const viewport = page.viewportSize();
  expect(box).not.toBeNull();
  expect(box.width).toBeGreaterThan(viewport.width * 0.9);
});

test('can open a file on a mobile viewport', async ({ page }) => {
  await page.locator('.tree-row', { hasText: 'README.md' }).click();
  await expect(page.locator('.code-view')).toBeVisible();
  await expect(page.locator('.code-view .code')).toContainText('Tasklite');
});

test('find button opens the palette and matches files', async ({ page }) => {
  await page.getByRole('button', { name: 'Find files' }).click();
  await expect(page.locator('#palette')).toBeVisible();
  await page.locator('#palette-input').fill('main.css');
  await expect(page.locator('.palette-row').first()).toContainText('main.css');
});

test('header action buttons meet a comfortable touch-target height', async ({ page }) => {
  const box = await page.locator('#find-btn').boundingBox();
  expect(box).not.toBeNull();
  expect(box.height).toBeGreaterThanOrEqual(38);
});

test('can create, edit, stage, and commit a file on a mobile viewport', async ({ page }) => {
  // Drive the editor from the sidebar's New file button (always in view on
  // mobile) rather than the in-header Edit action, then commit.
  await page.locator('#new-file-btn').click();
  await expect(page.locator('#newfile-overlay')).toBeVisible();
  await page.locator('#newfile-input').fill('mobile/note.md');
  await page.locator('#newfile-create').click();

  const area = page.locator('.editor-area');
  await expect(area).toBeVisible();
  await area.fill('# Written on mobile\n');
  await page.getByRole('button', { name: 'Save', exact: true }).click();
  await expect(page.locator('#changes-count')).toHaveText('1');

  await page.locator('#changes-btn').click();
  await expect(page.locator('#changes-panel')).toBeVisible();
  await page.locator('#commit-message').fill('Add mobile note');
  await page.locator('#commit-btn').click();
  await expect(page.locator('#toast')).toContainText(/Committed/);
  await expect(page.locator('#changes-count')).toBeHidden();
});
