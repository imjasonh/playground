import { test, expect } from '@playwright/test';
import { buildSampleLineFeed, buildSampleAlertsFeed } from '../src/sampleFeed.js';
import { complexById } from '../src/stations.js';

test.beforeEach(async ({ page }) => {
  await page.goto('/');
});

test('boots in sample mode and renders the full board', async ({ page }) => {
  await expect(page.locator('#data-mode')).toHaveText('Sample data');
  await expect(page.locator('#station-name')).toHaveText('Times Sq - 42 St');

  // 24 service-status pills (one per line).
  await expect(page.locator('.route-pill')).toHaveCount(24);

  // Arrival board has live countdowns in both directions.
  await expect(page.locator('.arrival-row').first()).toBeVisible();
  await expect(page.locator('.lane').nth(0).locator('.arrival-row').first()).toBeVisible();
  await expect(page.locator('.lane').nth(1).locator('.arrival-row').first()).toBeVisible();

  // Trains in service + alerts populated.
  await expect(page.locator('.train-row').first()).toBeVisible();
  await expect(page.locator('.alert').first()).toBeVisible();
});

test('sample alerts show A delays and G no-service', async ({ page }) => {
  const aPill = page.locator('.route-pill', { hasText: 'Delays' }).first();
  await expect(aPill).toBeVisible();
  // Tapping a line filters the alerts list to that line.
  await page.locator('.route-pill').filter({ has: page.locator('.dot.bad') }).first().click();
  await expect(page.locator('#alerts .alert').first()).toBeVisible();
});

test('searching selects a different station', async ({ page }) => {
  await page.locator('#station-search').click();
  await page.locator('#station-search').fill('Bedford Av');
  const option = page.locator('#station-results .result', { hasText: 'Bedford Av' }).first();
  await expect(option).toBeVisible();
  await option.click();
  await expect(page.locator('#station-name')).toContainText('Bedford Av');
});

test('popular-station chips switch stations', async ({ page }) => {
  const chip = page.locator('#station-chips .chip').first();
  const name = await chip.textContent();
  await chip.click();
  await expect(page.locator('#station-name')).toHaveText(name.trim());
});

test('live mode decodes intercepted GTFS-realtime protobuf', async ({ page }) => {
  const now = Date.now();
  const lineBytes = buildSampleLineFeed({ now, complex: complexById('611') });
  const alertBytes = buildSampleAlertsFeed({ now });

  await page.route(/api-endpoint\.mta\.info/, async (route) => {
    const isAlerts = route.request().url().includes('camsys');
    await route.fulfill({
      status: 200,
      headers: { 'content-type': 'application/x-protobuf', 'access-control-allow-origin': '*' },
      body: Buffer.from(isAlerts ? alertBytes : lineBytes),
    });
  });

  await page.locator('#settings > summary').click();
  // Direct requests so the route matcher above intercepts the MTA URL.
  await page.selectOption('#proxy-select', 'direct');
  await page.getByRole('radio', { name: /Live/ }).check();

  await expect(page.locator('#data-mode')).toHaveText('Live');
  await expect(page.locator('.arrival-row').first()).toBeVisible();
  await expect(page.locator('#error')).toBeHidden();
});
