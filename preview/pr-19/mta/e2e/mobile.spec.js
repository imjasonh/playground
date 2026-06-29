import { test, expect } from '@playwright/test';

test.beforeEach(async ({ page }) => {
  await page.goto('/');
});

test('renders a usable single-column layout on mobile', async ({ page }) => {
  await expect(page.locator('#station-name')).toHaveText('Times Sq - 42 St');
  await expect(page.locator('.arrival-row').first()).toBeVisible();

  // Cards stack vertically: the status card sits below the station card.
  const station = await page.locator('.station-card').boundingBox();
  const status = await page.locator('.status-card').boundingBox();
  expect(station).not.toBeNull();
  expect(status).not.toBeNull();
  expect(status.y).toBeGreaterThan(station.y + station.height - 1);
});

test('arrival lanes stack on a narrow viewport', async ({ page }) => {
  const lanes = page.locator('.arrivals .lane');
  await expect(lanes).toHaveCount(2);
  const first = await lanes.nth(0).boundingBox();
  const second = await lanes.nth(1).boundingBox();
  expect(second.y).toBeGreaterThan(first.y + first.height - 1);
});

test('station search works on touch', async ({ page }) => {
  await page.locator('#station-search').fill('Coney Island');
  const option = page.locator('#station-results .result', { hasText: 'Coney Island' }).first();
  await expect(option).toBeVisible();
  await option.click();
  await expect(page.locator('#station-name')).toContainText('Coney Island');
});

test('refresh button is a comfortable touch target', async ({ page }) => {
  const box = await page.locator('#refresh-btn').boundingBox();
  expect(box).not.toBeNull();
  expect(box.height).toBeGreaterThanOrEqual(38);
});
