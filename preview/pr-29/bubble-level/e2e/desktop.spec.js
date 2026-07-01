import { test, expect } from '@playwright/test';

function cssVar(page, selector, name) {
  return page
    .locator(selector)
    .evaluate((el, n) => parseFloat(el.style.getPropertyValue(n) || '0'), name);
}

async function dragBullseye(page, fractionX, fractionY) {
  const box = await page.locator('#bullseye').boundingBox();
  const startX = box.x + box.width / 2;
  const startY = box.y + box.height / 2;
  await page.mouse.move(startX, startY);
  await page.mouse.down();
  await page.mouse.move(
    box.x + box.width * fractionX,
    box.y + box.height * fractionY,
    { steps: 10 },
  );
  await page.mouse.up();
}

test.beforeEach(async ({ page }) => {
  await page.goto('/');
  await expect(page.locator('#bullseye')).toBeVisible();
  // A desktop browser has no gyroscope, so the app falls back to a preview.
  await expect(page.locator('#status')).toContainText(/preview/i, { timeout: 6000 });
});

test('no permission gate is shown on desktop', async ({ page }) => {
  await expect(page.locator('#enable-panel')).toBeHidden();
});

test('dragging the dial to the right floats the bubble right', async ({ page }) => {
  await dragBullseye(page, 0.85, 0.5);
  await expect.poll(() => cssVar(page, '#bubble', '--bx')).toBeGreaterThan(0.3);
});

test('dragging the dial downward floats the bubble down', async ({ page }) => {
  await dragBullseye(page, 0.5, 0.85);
  await expect.poll(() => cssVar(page, '#bubble', '--by')).toBeGreaterThan(0.3);
});

test('arrow keys nudge the bubble and 0 re-centers it', async ({ page }) => {
  await page.keyboard.press('0');
  for (let i = 0; i < 6; i += 1) {
    await page.keyboard.press('ArrowUp');
  }
  await expect.poll(() => cssVar(page, '#bubble', '--by')).toBeLessThan(-0.15);

  await page.keyboard.press('0');
  await expect
    .poll(async () => Math.abs(await cssVar(page, '#bubble', '--by')))
    .toBeLessThan(0.1);
});

test('calibrating in preview re-zeroes the current tilt', async ({ page }) => {
  await dragBullseye(page, 0.85, 0.5);
  await expect.poll(() => cssVar(page, '#bubble', '--bx')).toBeGreaterThan(0.3);

  await page.locator('#calibrate-btn').click();
  await expect(page.locator('#status')).toContainText(/calibrat/i);
  await expect(page.locator('#reset-btn')).toBeEnabled();
  await expect(page.locator('#level-badge')).toHaveText(/level/i);
  await expect
    .poll(async () => Math.abs(await cssVar(page, '#bubble', '--bx')))
    .toBeLessThan(0.15);
});
