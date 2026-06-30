import { expect, test } from "@playwright/test";
import { createServedRepo, startGitHTTPServer } from "./git-http-server.js";

let fixture;
let gitServer;

test.beforeAll(async () => {
  fixture = createServedRepo();
  gitServer = await startGitHTTPServer(fixture.root);
});

test.afterAll(async () => {
  await gitServer?.close();
  fixture?.cleanup();
});

async function loadRepository(page) {
  await page.goto("/");
  await expect(page.locator("#runtime-status")).toHaveText(
    "Go/WASM + SQLite ready",
    { timeout: 60_000 },
  );
  await page.locator("#repository-url").fill(
    `${gitServer.url}/${fixture.repoPath}`,
  );
  await page.locator("#repository-form summary").click();
  await page.locator("#cors-proxy").fill("");
  await page.locator("#clone-depth").fill("0");
  await page.locator("#load-repository").click();
  await expect(page.locator("#clone-status")).toHaveText(
    "Repository loaded. SQL tables are ready.",
    { timeout: 60_000 },
  );
  await expect(page.locator("#result-summary")).toContainText("2 rows");
}

test("runs the real gitdb virtual tables in WebAssembly", async ({ page }) => {
  const pageErrors = [];
  page.on("pageerror", (error) => pageErrors.push(error.message));

  await loadRepository(page);
  await expect(page.locator("#result-summary")).toContainText("2 rows");
  await expect(page.locator("#result-table")).toContainText("Update real data");
  await expect(page.locator("#result-table")).toContainText("Initial live commit");

  await page.locator("#sql-input").fill(
    "SELECT name, type FROM tags ORDER BY name;",
  );
  await page.locator("#run-query").click();
  await expect(page.getByRole("columnheader", { name: "type" })).toBeVisible();
  await expect(page.locator("#result-table")).toContainText("v1.0");

  expect(pageErrors).toEqual([]);
});

test("surfaces SQLite errors without terminating the worker", async ({ page }) => {
  await loadRepository(page);

  await page.locator("#sql-input").fill("SELECT * FROM definitely_missing;");
  await page.locator("#run-query").click();
  await expect(page.locator("#error-panel")).toContainText(
    "no such table: definitely_missing",
  );

  await page.locator("#sql-input").fill("SELECT count(*) AS files FROM files;");
  await page.locator("#run-query").click();
  await expect(page.getByRole("columnheader", { name: "files" })).toBeVisible();
  await expect(page.locator("#result-table tbody td")).toHaveText("2");
});

test("executes every bundled virtual-table example", async ({ page }) => {
  await loadRepository(page);

  const examples = [
    ["authors", "lines_added"],
    ["files", "path"],
    ["changes", "change"],
    ["blame", "line_no"],
    ["planner", "detail"],
    ["network", "http_status"],
  ];
  for (const [example, expectedColumn] of examples) {
    await page.locator("#example-select").selectOption(example);
    await page.locator("#run-query").click();
    await expect(
      page.getByRole("columnheader", { name: expectedColumn }),
    ).toBeVisible();
    await expect(page.locator("#error-panel")).toBeHidden();
  }
});
