import { expect, test as base } from "@playwright/test";

const test = base.extend({
  page: async ({ page }, use) => {
    const failures = [];
    page.on("console", (message) => {
      if (message.type() === "error") failures.push(`console: ${message.text()}`);
    });
    page.on("pageerror", (error) => failures.push(`page: ${error.message}`));
    page.on("requestfailed", (request) => {
      if (request.url().startsWith("http://127.0.0.1")) {
        failures.push(`request: ${request.url()} (${request.failure()?.errorText})`);
      }
    });
    await page.goto("/");
    await use(page);
    expect(failures, failures.join("\n")).toEqual([]);
  },
});

test("renders the narrative and all interactive passages", async ({ page }) => {
  await expect(page).toHaveTitle(/Inside Bubble Man Stage/);
  await expect(page.getByRole("heading", { level: 1 })).toContainText("791");

  const tabs = page.getByRole("tab");
  await expect(tabs).toHaveCount(4);
  await expect(tabs.nth(0)).toHaveAttribute("aria-selected", "true");
  await expect(page.locator(".passage-title")).toContainText("quiet opening");
  await expect(page.locator(".sequence-row")).toHaveCount(4);
  await expect(page.locator(".code-row")).toHaveCount(10);
  await expect(page.locator(".total-time")).toHaveText("0:05.3");
});

test("switches passages with mouse and keyboard", async ({ page }) => {
  const intro = page.getByRole("tab", { name: /INTRO/ });
  const ostinato = page.getByRole("tab", { name: /OSTINATO/ });
  const lead = page.getByRole("tab", { name: /LEAD/ });

  await lead.click();
  await expect(lead).toHaveAttribute("aria-selected", "true");
  await expect(page.locator(".passage-title")).toContainText("Three lines");
  await expect(page.locator(".code-list")).toContainText("NOTE_DELAY 1");

  await intro.click();
  await intro.press("ArrowRight");
  await expect(ostinato).toHaveAttribute("aria-selected", "true");
  await expect(ostinato).toBeFocused();
  await expect(page.locator(".passage-title")).toContainText("machinery continues");
});

test("produces an audio signal, follows bytecode, mutes, and stops cleanly", async ({ page }) => {
  const play = page.getByRole("button", { name: "Play passage" });
  await play.click();

  await expect(page.getByRole("button", { name: "Stop" })).toBeVisible();
  await expect(page.locator(".live-indicator")).toHaveClass(/is-live/);
  await expect(page.locator(".current-time")).not.toHaveText("0:00.0", { timeout: 2_000 });
  await expect(page.locator(".player-shell")).toHaveAttribute("data-audio-active", "true", {
    timeout: 3_000,
  });
  await expect(page.locator(".audio-status")).toContainText("Audio output active");
  await expect(page.locator(".code-row.is-active")).toHaveCount(1);
  await expect(page.locator(".note-block.is-active").first()).toBeVisible();

  const mute = page.getByRole("button", { name: "MUTE PULSE 1" });
  await mute.click();
  await expect(mute).toHaveAttribute("aria-pressed", "true");
  await expect(page.locator('.sequence-row[data-channel="pulse1"]')).toHaveClass(/is-muted/);

  await page.getByRole("button", { name: "Stop" }).click();
  await expect(page.getByRole("button", { name: "Play passage" })).toBeVisible();
  await expect(page.locator(".current-time")).toHaveText("0:00.0");
  await expect(page.locator(".code-row.is-active")).toHaveCount(0);
});

test("switching passage while playing resets transport", async ({ page }) => {
  await page.getByRole("button", { name: "Play passage" }).click();
  await expect(page.getByRole("button", { name: "Stop" })).toBeVisible();

  await page.getByRole("tab", { name: /TURNAROUND/ }).click();
  await expect(page.getByRole("button", { name: "Play passage" })).toBeVisible();
  await expect(page.locator(".current-time")).toHaveText("0:00.0");
  await expect(page.locator(".code-list")).toContainText("G7");
});

test("decoder exposes the byte split and reverse-engineering caveat", async ({ page }) => {
  await page.getByRole("link", { name: "Decode" }).click();
  await expect(page.locator(".hex-byte")).toHaveText("CC");
  await expect(page.locator(".binary-byte span")).toHaveCount(8);
  await expect(page.locator(".opcode-row")).toHaveCount(10);
  await expect(page.locator(".technical-note")).toContainText("not Capcom’s original symbols");
});

test("mobile layout has no page-level horizontal overflow", async ({ page }, testInfo) => {
  test.skip(!testInfo.project.name.startsWith("mobile"), "mobile-only assertion");
  const dimensions = await page.evaluate(() => ({
    clientWidth: document.documentElement.clientWidth,
    scrollWidth: document.documentElement.scrollWidth,
  }));
  expect(dimensions.scrollWidth).toBe(dimensions.clientWidth);

  await page.getByRole("link", { name: /Begin the playable walkthrough/ }).click();
  await expect(page).toHaveURL(/#walkthrough$/);
  const playButton = page.getByRole("button", { name: "Play passage" });
  await playButton.scrollIntoViewIfNeeded();
  await expect(playButton).toBeInViewport();
  await expect(page.locator(".bytecode-panel")).toBeVisible();
});
