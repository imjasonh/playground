import { test, expect } from '@playwright/test';

// Mobile tests use the #repo=demo deep link to auto-load the demo repo.

test.beforeEach(async ({ page }) => {
  await page.goto('/#repo=demo');
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
  await page.locator('#tree-filter').fill('storage.js');
  await page.locator('.flat-row', { hasText: 'storage.js' }).click();
  await expect(page.locator('.code-view')).toBeVisible();
  await expect(page.locator('.code-view .code')).toContainText('loadTasks');
});

test('renders a Markdown preview on a mobile viewport', async ({ page }) => {
  // Locate README.md via the filter so the test doesn't depend on where the row
  // lands in the virtualized tree on a short viewport.
  await page.locator('#tree-filter').fill('README.md');
  await page.locator('.flat-row', { hasText: 'README.md' }).click();
  await expect(page.locator('.markdown-body')).toBeVisible();
  await expect(page.locator('.markdown-body h1')).toHaveText('Tasklite');
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
