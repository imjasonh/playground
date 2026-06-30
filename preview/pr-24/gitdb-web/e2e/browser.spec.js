import { expect, test } from "@playwright/test";

test("runs the real gitdb virtual tables in WebAssembly", async ({ page }) => {
  const pageErrors = [];
  page.on("pageerror", (error) => pageErrors.push(error.message));

  await page.goto("/");
  await expect(page.locator("#runtime-status")).toHaveText(
    "Go/WASM + SQLite ready",
    { timeout: 60_000 },
  );
  await expect(page.locator("#result-summary")).toContainText("2 rows");
  await expect(page.locator("#result-table")).toContainText("Bob");
  await expect(page.locator("#result-table")).toContainText("Alice");

  await page.locator("#sql-input").fill(
    "SELECT count(*) AS commits FROM commits WHERE ref = 'prototype';",
  );
  await page.locator("#run-query").click();
  await expect(page.locator("#result-table th")).toHaveText("commits");
  await expect(page.locator("#result-table td")).toHaveText("1");

  expect(pageErrors).toEqual([]);
});

test("surfaces SQLite errors without terminating the worker", async ({ page }) => {
  await page.goto("/");
  await expect(page.locator("#runtime-status")).toHaveText(
    "Go/WASM + SQLite ready",
    { timeout: 60_000 },
  );

  await page.locator("#sql-input").fill("SELECT * FROM definitely_missing;");
  await page.locator("#run-query").click();
  await expect(page.locator("#error-panel")).toContainText(
    "no such table: definitely_missing",
  );

  await page.locator("#sql-input").fill("SELECT count(*) AS files FROM files;");
  await page.locator("#run-query").click();
  await expect(page.locator("#result-table td")).toHaveText("4");
});
