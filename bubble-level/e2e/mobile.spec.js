import { test, expect } from '@playwright/test';

// Drive the level by dispatching synthetic DeviceOrientationEvents, since a
// headless browser has no real gyroscope.
async function setOrientation(page, { beta = 0, gamma = 0, alpha = 0 } = {}) {
  await page.evaluate((reading) => {
    window.dispatchEvent(new DeviceOrientationEvent('deviceorientation', {
      ...reading,
      absolute: true,
    }));
  }, { beta, gamma, alpha });
}

function cssVar(page, selector, name) {
  return page
    .locator(selector)
    .evaluate((el, n) => parseFloat(el.style.getPropertyValue(n) || '0'), name);
}

test.beforeEach(async ({ page }) => {
  await page.goto('/');
  await expect(page.locator('#bullseye')).toBeVisible();
});

test('does not show the iOS permission gate on Android/Chromium', async ({ page }) => {
  await expect(page.locator('#enable-panel')).toBeHidden();
});

test('a flat reading reports level', async ({ page }) => {
  await setOrientation(page, { beta: 0, gamma: 0 });
  await expect(page.locator('#tilt-value')).toHaveText('0.0');
  await expect(page.locator('#level-badge')).toHaveText(/level/i);
  await expect(page.locator('body')).toHaveClass(/is-level/);
});

test('raising the right edge floats the bubble to the right', async ({ page }) => {
  await setOrientation(page, { beta: 0, gamma: -20 });
  await expect.poll(() => cssVar(page, '#bubble', '--bx')).toBeGreaterThan(0.3);
  await expect.poll(() => cssVar(page, '#tube-h-bubble', '--bx')).toBeGreaterThan(0.3);
  await expect(page.locator('body')).not.toHaveClass(/is-level/);
});

test('raising the top edge floats the bubble up the screen', async ({ page }) => {
  await setOrientation(page, { beta: 20, gamma: 0 });
  await expect.poll(() => cssVar(page, '#bubble', '--by')).toBeLessThan(-0.3);
  await expect.poll(() => cssVar(page, '#tube-v-bubble', '--by')).toBeLessThan(-0.3);
});

test('the tilt readout grows with a bigger tilt', async ({ page }) => {
  await setOrientation(page, { beta: 0, gamma: 25 });
  await expect
    .poll(() => page.locator('#tilt-value').textContent().then(Number))
    .toBeGreaterThan(20);
  await expect(page.locator('#level-badge')).toHaveText(/off by/i);
});

test('calibration zeroes out the current surface', async ({ page }) => {
  await setOrientation(page, { beta: 3, gamma: 3 });
  await expect
    .poll(() => page.locator('#tilt-value').textContent().then(Number))
    .toBeGreaterThan(2);

  await expect(page.locator('#reset-btn')).toBeDisabled();
  await page.locator('#calibrate-btn').tap();

  await expect(page.locator('#status')).toContainText(/calibrat/i);
  await expect(page.locator('#reset-btn')).toBeEnabled();
  await expect(page.locator('#level-badge')).toHaveText(/level/i);
  await expect
    .poll(async () => Math.abs(await cssVar(page, '#bubble', '--bx')))
    .toBeLessThan(0.15);

  await page.locator('#reset-btn').tap();
  await expect(page.locator('#status')).toContainText(/reset/i);
  await expect(page.locator('#level-badge')).toHaveText(/off by/i);
});

test('compensates for landscape screen rotation', async ({ page }) => {
  // Make screen.orientation.angle scriptable so we can simulate turning the phone.
  await page.addInitScript(() => {
    let angle = 0;
    try {
      Object.defineProperty(window.screen.orientation, 'angle', {
        configurable: true,
        get: () => angle,
      });
    } catch {
      // If the property can't be shadowed the test will surface it below.
    }
    window.__setScreenAngle = (value) => {
      angle = value;
    };
  });
  await page.reload();
  await expect(page.locator('#bullseye')).toBeVisible();

  // Portrait: raising the natural right edge floats the bubble right.
  await page.evaluate(() => window.__setScreenAngle(0));
  await setOrientation(page, { beta: 0, gamma: -20 });
  await expect.poll(() => cssVar(page, '#bubble', '--bx')).toBeGreaterThan(0.3);

  // Turn the phone to landscape: the same physical tilt should now float the
  // bubble UP the screen, not sideways.
  await page.evaluate(() => window.__setScreenAngle(90));
  await expect.poll(() => cssVar(page, '#bubble', '--by')).toBeLessThan(-0.3);
  await expect
    .poll(async () => Math.abs(await cssVar(page, '#bubble', '--bx')))
    .toBeLessThan(0.15);
});

test('tabs switch between the surface, horizontal, and vertical levels', async ({ page }) => {
  await expect(page.locator('#tab-surface')).toHaveAttribute('aria-selected', 'true');
  await expect(page.locator('#panel-surface')).toBeVisible();
  await expect(page.locator('#panel-horizontal')).toBeHidden();

  await page.locator('#tab-horizontal').tap();
  await expect(page.locator('#tab-horizontal')).toHaveAttribute('aria-selected', 'true');
  await expect(page.locator('#tube-h')).toBeVisible();
  await expect(page.locator('#panel-surface')).toBeHidden();

  await page.locator('#tab-vertical').tap();
  await expect(page.locator('#tab-vertical')).toHaveAttribute('aria-selected', 'true');
  await expect(page.locator('#tube-v')).toBeVisible();
  await expect(page.locator('#panel-horizontal')).toBeHidden();
});

test('remembers the selected level across reloads', async ({ page }) => {
  await page.locator('#tab-vertical').tap();
  await expect(page.locator('#tab-vertical')).toHaveAttribute('aria-selected', 'true');

  await page.reload();
  await expect(page.locator('#tab-vertical')).toHaveAttribute('aria-selected', 'true');
  await expect(page.locator('#tube-v')).toBeVisible();
  await expect(page.locator('#panel-surface')).toBeHidden();
});

test('control buttons meet the minimum touch-target height', async ({ page }) => {
  const box = await page.locator('#calibrate-btn').boundingBox();
  expect(box).not.toBeNull();
  expect(box.height).toBeGreaterThanOrEqual(44);
});
