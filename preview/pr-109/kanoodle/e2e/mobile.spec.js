import { test, expect } from '@playwright/test';

async function startFreePlay(page) {
  const panel = page.locator('.settings-panel');
  if (!(await panel.evaluate((el) => el.open))) {
    await panel.locator('summary').click();
  }
  await page.selectOption('#difficulty', '6');
  await page.locator('#new-game').click();
  await expect(page.locator('.tray-piece').first()).toBeVisible();
}

test.beforeEach(async ({ page }) => {
  await page.goto('/');
  await expect(page.locator('.cell')).toHaveCount(55);
});

test('shows touch-friendly hint on mobile viewport', async ({ page }) => {
  await expect(page.locator('#interaction-hint')).toContainText(/tap/i);
  await expect(page.locator('body')).toHaveClass(/touch-mode/);
});

test('tap-to-select and tap-to-place a piece', async ({ page }) => {
  await startFreePlay(page);
  const trayCountBefore = await page.locator('.tray-piece').count();
  const firstTrayPiece = page.locator('.tray-piece').first();
  const pieceId = await firstTrayPiece.getAttribute('data-piece-id');

  await firstTrayPiece.tap();
  await expect(firstTrayPiece).toHaveClass(/selected/);
  await expect(page.locator('#status')).toContainText(`Selected: ${pieceId}`);

  await page.locator('.cell[data-row="2"][data-col="5"]').tap();

  await expect(page.locator('.tray-piece')).toHaveCount(trayCountBefore - 1);
});

test('rotate and return buttons work after selecting a piece', async ({ page }) => {
  await startFreePlay(page);
  const firstTrayPiece = page.locator('.tray-piece').first();
  await firstTrayPiece.tap();

  await expect(page.locator('#rotate-btn')).toBeEnabled();
  await expect(page.locator('#flip-btn')).toBeEnabled();

  await page.locator('#rotate-btn').tap();
  await page.locator('#return-btn').tap();

  await expect(firstTrayPiece).not.toHaveClass(/selected/);
});

test('page scrolls on mobile so tray and board are both reachable', async ({ page }) => {
  await startFreePlay(page);

  const metrics = await page.evaluate(() => ({
    scrollHeight: document.documentElement.scrollHeight,
    innerHeight: window.innerHeight,
  }));

  expect(metrics.scrollHeight).toBeGreaterThan(metrics.innerHeight);

  await page.evaluate(() => window.scrollTo(0, document.documentElement.scrollHeight));
  await expect(page.locator('.board-wrap')).toBeInViewport();
});

test('board fits within mobile viewport width', async ({ page }) => {
  const board = page.locator('.board');
  const viewport = page.viewportSize();
  const box = await board.boundingBox();
  expect(box).not.toBeNull();
  expect(box.width).toBeLessThanOrEqual(viewport.width);
});

test('control buttons meet minimum touch target height', async ({ page }) => {
  const rotateBtn = page.locator('#rotate-btn');
  const box = await rotateBtn.boundingBox();
  expect(box).not.toBeNull();
  expect(box.height).toBeGreaterThanOrEqual(44);
});
