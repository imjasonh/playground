import { test, expect } from '@playwright/test';
import AxeBuilder from '@axe-core/playwright';

// Automated accessibility regression checks (axe-core) for the demo-driven UI.
// We assert against the full WCAG 2.0/2.1 A and AA rule sets (color-contrast
// included) so a future change that drops a role/label, breaks a name, or dims
// text below 4.5:1 is caught here.

async function loadDemo(page) {
  await page.goto('/');
  await page.getByRole('button', { name: 'Try a demo (no network)' }).click();
  await expect(page.locator('#browser-view')).toBeVisible();
}

const TAGS = ['wcag2a', 'wcag2aa', 'wcag21a', 'wcag21aa'];

function scan(page, root) {
  const builder = new AxeBuilder({ page }).withTags(TAGS);
  return root ? builder.include(root).analyze() : builder.analyze();
}

test('start / clone screen has no a11y violations', async ({ page }) => {
  await page.goto('/');
  await expect(page.locator('#start-view')).toBeVisible();
  const results = await scan(page);
  expect(results.violations).toEqual([]);
});

test('demo browser (tree + viewer) has no a11y violations', async ({ page }) => {
  await loadDemo(page);
  await page.locator('.tree-row', { hasText: 'README.md' }).click();
  await expect(page.locator('#file-path')).toContainText('README.md');

  const results = await scan(page);
  expect(results.violations).toEqual([]);
});

test('command palette has no a11y violations', async ({ page }) => {
  await loadDemo(page);
  await page.getByRole('button', { name: 'Find files' }).click();
  await expect(page.locator('#palette')).toBeVisible();
  await page.locator('#palette-input').fill('render');
  await expect(page.locator('.palette-row').first()).toBeVisible();

  const results = await scan(page, '#palette');
  expect(results.violations).toEqual([]);
});

test('history panel has no a11y violations', async ({ page }) => {
  await loadDemo(page);
  await page.getByRole('button', { name: 'History' }).click();
  await expect(page.locator('#history-panel')).toBeVisible();
  await expect(page.locator('.commit-item').first()).toBeVisible();

  const results = await scan(page, '#history-panel');
  expect(results.violations).toEqual([]);
});
