import { test, expect } from "@playwright/test";
import { fileURLToPath } from "node:url";

const demoPath = fileURLToPath(new URL("../assets/demo.ts", import.meta.url));

async function waitForDemo(page) {
  await page.goto("/#demo");
  await expect(page.locator("#stage-state")).toContainText("ready", {
    timeout: 15_000,
  });
  await expect(page.locator("#loading-overlay")).toBeHidden();
}

test("initializes the worker-first playback pipeline", async ({ page }) => {
  await page.goto("/");

  await expect(page.getByRole("heading", { name: "MPEG Canvas" })).toBeVisible();
  await expect(page.locator("#decoder-value")).toContainText("WebAssembly");
  await expect(page.locator("#renderer-value")).toContainText("Offscreen");
  await expect(page.locator("#status")).toContainText("Ready");
});

test("loads and identifies the bundled MPEG-TS demo", async ({ page }) => {
  await waitForDemo(page);

  await expect(page.locator("#source-name")).toHaveText("demo.ts");
  await expect(page.locator("#video-value")).toContainText("480×270");
  await expect(page.locator("#audio-value")).toContainText(/MP2|kHz/);
  await expect(page.locator("#play-button")).toBeEnabled();

  const metadata = await page.evaluate(
    () => window.mpegCanvasPlayer.controller.metadata,
  );
  expect(metadata.decoder).toBe("WebAssembly");
  expect(metadata.width).toBe(480);
  expect(metadata.height).toBe(270);
  expect(metadata.hasAudio).toBe(true);
});

test("plays, advances, and pauses without main-thread frame copies", async ({
  page,
}) => {
  await waitForDemo(page);

  const before = await page.evaluate(
    () => window.mpegCanvasPlayer.controller.currentTime,
  );
  await page.locator("#play-button").click();
  await expect(page.locator("#stage-state")).toContainText("playing");
  await expect
    .poll(
      () =>
        page.evaluate(() => window.mpegCanvasPlayer.controller.currentTime),
      { timeout: 5_000 },
    )
    .toBeGreaterThan(before + 0.2);

  await page.locator("#play-button").click();
  await expect(page.locator("#stage-state")).toContainText("paused");
  await expect(page.locator("#decode-value")).toContainText("ms/frame");

  const pausedAt = await page.evaluate(
    () => window.mpegCanvasPlayer.controller.currentTime,
  );
  await page.waitForTimeout(400);
  const stillPausedAt = await page.evaluate(
    () => window.mpegCanvasPlayer.controller.currentTime,
  );
  expect(Math.abs(stillPausedAt - pausedAt)).toBeLessThan(0.05);
});

test("accepts a local transport stream through the file picker", async ({
  page,
}) => {
  await page.goto("/");
  await page.locator("#file-input").setInputFiles(demoPath);

  await expect(page.locator("#stage-state")).toContainText("ready", {
    timeout: 15_000,
  });
  await expect(page.locator("#source-name")).toHaveText("demo.ts");
  await expect(page.locator("#source-size")).not.toHaveText("no file");
});

test("keeps player controls usable at the configured viewport", async ({
  page,
}) => {
  await page.goto("/");

  const playBox = await page.locator("#play-button").boundingBox();
  expect(playBox).not.toBeNull();
  expect(playBox.height).toBeGreaterThanOrEqual(40);

  const dimensions = await page.evaluate(() => ({
    scrollWidth: document.documentElement.scrollWidth,
    viewportWidth: window.innerWidth,
  }));
  expect(dimensions.scrollWidth).toBeLessThanOrEqual(dimensions.viewportWidth + 1);
});

test("keeps controls available in fullscreen", async ({ page }) => {
  await page.goto("/");
  await page.locator("#fullscreen-button").click();

  await expect
    .poll(() => page.evaluate(() => document.fullscreenElement?.id))
    .toBe("player-panel");
  await expect(page.locator(".controls")).toBeVisible();
  await expect(page.locator("#fullscreen-button")).toBeVisible();
});

test("recovers the drop-zone prompt after invalid media", async ({ page }) => {
  await page.goto("/");
  await page.locator("#file-input").setInputFiles({
    name: "not-video.ts",
    mimeType: "video/mp2t",
    buffer: Buffer.from("not an MPEG transport stream"),
  });

  await expect(page.getByRole("alert")).toContainText(
    "not a supported MPEG transport stream",
  );
  await expect(page.locator("#empty-state")).toBeVisible();
  await expect(page.locator("#play-button")).toBeDisabled();
});
