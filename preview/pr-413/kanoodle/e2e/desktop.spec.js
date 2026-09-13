import { test, expect } from '@playwright/test';

test('shows drag hint on desktop viewport', async ({ page }) => {
  await page.goto('/');
  await expect(page.locator('#interaction-hint')).toContainText(/drag/i);
  await expect(page.locator('body')).not.toHaveClass(/touch-mode/);
});

test('drag-and-drop places a piece', async ({ page }) => {
  await page.goto('/');
  await page.selectOption('#difficulty', '6');
  await page.locator('#new-game').click();

  const trayCountBefore = await page.locator('.tray-piece').count();
  const firstTrayPiece = page.locator('.tray-piece').first();
  const targetCell = page.locator('.cell[data-row="2"][data-col="5"]');

  const trayBox = await firstTrayPiece.boundingBox();
  const cellBox = await targetCell.boundingBox();
  expect(trayBox).not.toBeNull();
  expect(cellBox).not.toBeNull();

  await page.mouse.move(trayBox.x + trayBox.width / 2, trayBox.y + trayBox.height / 2);
  await page.mouse.down();
  await page.mouse.move(cellBox.x + cellBox.width / 2, cellBox.y + cellBox.height / 2, { steps: 10 });
  await page.mouse.up();

  await expect(page.locator('.tray-piece')).toHaveCount(trayCountBefore - 1);
});
