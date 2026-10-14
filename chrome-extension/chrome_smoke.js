import { spawn } from "node:child_process";
import { mkdtemp, readFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { setTimeout as delay } from "node:timers/promises";

import { actionTitle, badgeText, duplicateTabIds } from "./duplicates.js";

const root = path.dirname(new URL(import.meta.url).pathname);
const chromeBin = process.env.CHROME_BIN || "google-chrome";

function connect(wsUrl) {
  const ws = new WebSocket(wsUrl);
  let next = 0;
  const pending = new Map();
  const opened = new Promise((resolve, reject) => {
    ws.addEventListener("open", () => resolve());
    ws.addEventListener("error", () => reject(new Error(`websocket failed for ${wsUrl}`)));
  });
  ws.addEventListener("message", (event) => {
    const message = JSON.parse(event.data);
    if (!message.id || !pending.has(message.id)) {
      return;
    }
    const waiter = pending.get(message.id);
    pending.delete(message.id);
    if (message.error) {
      waiter.reject(new Error(JSON.stringify(message.error)));
      return;
    }
    waiter.resolve(message.result);
  });
  return {
    async send(method, params = {}) {
      await opened;
      const id = next + 1;
      next = id;
      const result = new Promise((resolve, reject) => {
        pending.set(id, { resolve, reject });
      });
      ws.send(JSON.stringify({ id, method, params }));
      return result;
    },
    close() {
      ws.close();
    },
  };
}

async function debuggingPort(profile) {
  const deadline = Date.now() + 15000;
  while (Date.now() < deadline) {
    try {
      const text = await readFile(path.join(profile, "DevToolsActivePort"), "utf8");
      const port = text.split("\n")[0];
      if (port) {
        return port;
      }
    } catch (error) {
      const missing = error && error.code === "ENOENT";
      if (!missing) {
        throw error;
      }
    }
    await delay(100);
  }
  throw new Error("Chrome did not write DevToolsActivePort");
}

async function evaluate(session, expression) {
  if (!session.enabled) {
    await session.send("Runtime.enable");
    session.enabled = true;
    const deadline = Date.now() + 5000;
    while (Date.now() < deadline) {
      const probe = await session.send("Runtime.evaluate", {
        expression: "typeof chrome",
        returnByValue: true,
      });
      if (probe.result && probe.result.value === "object") {
        break;
      }
      await delay(100);
    }
  }
  const result = await session.send("Runtime.evaluate", {
    expression,
    awaitPromise: true,
    returnByValue: true,
  });
  if (result.exceptionDetails) {
    throw new Error(JSON.stringify(result.exceptionDetails));
  }
  return result.result.value;
}

async function targets(port) {
  return fetch(`http://127.0.0.1:${port}/json/list`).then((response) => response.json());
}

async function main() {
  const profile = await mkdtemp(path.join(tmpdir(), "chrome-extension-"));
  const child = spawn(
    chromeBin,
    [
      "--headless=new",
      "--no-sandbox",
      "--disable-gpu",
      "--disable-dev-shm-usage",
      "--no-first-run",
      "--no-default-browser-check",
      "--disable-background-networking",
      `--user-data-dir=${profile}`,
      "--remote-debugging-port=0",
    ],
    { stdio: ["ignore", "pipe", "pipe"] },
  );
  let logs = "";
  child.stderr.on("data", (chunk) => {
    logs += chunk.toString();
  });
  let browser = null;
  let workerSession = null;
  try {
    const port = await debuggingPort(profile);
    const version = await fetch(`http://127.0.0.1:${port}/json/version`).then((response) => response.json());
    browser = connect(version.webSocketDebuggerUrl);
    const loaded = await browser.send("Extensions.loadUnpacked", { path: root });
    const extensionId = loaded.id;
    await browser.send("Target.setDiscoverTargets", {
      discover: true,
      filter: [{ type: "tab" }, { type: "page" }],
    });
    const urls = ["https://example.com/notes", "https://example.com/notes", "https://example.com/other"];
    for (const url of urls) {
      await browser.send("Target.createTarget", { url });
    }
    const discovered = await browser.send("Target.getTargets");
    const tab = discovered.targetInfos.find(
      (target) => target.type === "tab" && target.url === "https://example.com/notes",
    );
    if (!tab) {
      throw new Error("Chrome did not expose a tab target for the duplicate page");
    }
    const deadline = Date.now() + 20000;
    let worker = null;
    while (Date.now() < deadline && !worker) {
      const list = await targets(port);
      worker = list.find(
        (target) => target.type === "service_worker" && target.url.startsWith(`chrome-extension://${extensionId}/`),
      );
      if (!worker) {
        await delay(200);
      }
    }
    if (!worker) {
      throw new Error(`service worker for ${extensionId} did not start\n${logs}`);
    }
    workerSession = connect(worker.webSocketDebuggerUrl);
    const name = await evaluate(workerSession, "chrome.runtime.getManifest().name");
    if (name !== "Close Duplicate Tabs") {
      throw new Error(`loaded ${extensionId} but the worker is ${name}`);
    }
    let observed = null;
    while (Date.now() < deadline) {
      observed = await evaluate(
        workerSession,
        `chrome.tabs.query({}).then(async (tabs) => ({
          tabs: tabs.map((tab) => ({
            id: tab.id,
            url: tab.url,
            pendingUrl: tab.pendingUrl,
            active: tab.active,
            pinned: tab.pinned,
            lastAccessed: tab.lastAccessed,
          })),
          text: await chrome.action.getBadgeText({}),
          title: await chrome.action.getTitle({}),
        }))`,
      );
      const count = duplicateTabIds(observed.tabs).length;
      if (observed.text === badgeText(count) && observed.title === actionTitle(count) && count > 0) {
        break;
      }
      observed = null;
      await delay(200);
    }
    if (!observed) {
      throw new Error(`badge did not match the open tabs\n${logs}`);
    }
    const menuError = await evaluate(
      workerSession,
      `new Promise((resolve) => {
        chrome.contextMenus.create({
          id: "close-duplicates",
          title: "probe",
          contexts: ["tab"],
        }, () => {
          resolve(chrome.runtime.lastError ? chrome.runtime.lastError.message : "created");
        });
      })`,
    );
    if (!String(menuError).includes("duplicate")) {
      throw new Error(`tab menu item was not registered: ${menuError}\n${logs}`);
    }
    console.log(`tab menu item close-duplicates is registered (${menuError})`);
    const before = observed.text;
    await browser.send("Extensions.triggerAction", { id: extensionId, targetId: tab.targetId });
    let after = null;
    while (Date.now() < deadline) {
      after = await evaluate(
        workerSession,
        `chrome.tabs.query({}).then(async (tabs) => ({
          tabs: tabs.map((tab) => ({ id: tab.id, url: tab.url, pendingUrl: tab.pendingUrl, active: tab.active, pinned: tab.pinned, lastAccessed: tab.lastAccessed })),
          text: await chrome.action.getBadgeText({}),
          title: await chrome.action.getTitle({}),
        }))`,
      );
      if (duplicateTabIds(after.tabs).length === 0 && after.text === "" && after.title === "No duplicate tabs") {
        console.log(
          `badge ${JSON.stringify(before)} then click cleared it across ${after.tabs.length} tabs`,
        );
        return;
      }
      await delay(200);
    }
    throw new Error(`click did not clear duplicate tabs: ${JSON.stringify(after)}\n${logs}`);
  } finally {
    if (workerSession) {
      workerSession.close();
    }
    if (browser) {
      browser.close();
    }
    child.kill();
    await Promise.race([
      new Promise((resolve) => child.once("exit", resolve)),
      delay(2000).then(() => child.kill("SIGKILL")),
    ]);
    await rm(profile, { recursive: true, force: true });
  }
}

main().catch((error) => {
  console.error(error instanceof Error ? error.message : error);
  process.exitCode = 1;
});
