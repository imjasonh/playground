import { test, expect } from '@playwright/test';

// Mobile tests use the #demo deep link to auto-load the demo repo.

test.beforeEach(async ({ page }) => {
  await page.goto('/#demo');
  await expect(page.locator('#browser-view')).toBeVisible();
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
