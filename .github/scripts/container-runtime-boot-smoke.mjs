// Boot a container2wasm runtime directory in a headless browser and prove the
// guest actually reaches a shell.
//
// This is the only automated check that the emulator built by
// container-runtime.yml works end to end. It cannot run in the iOS test suite:
// the emulator is hundreds of megabytes and is deliberately not in git, so
// CI's simulator build has no runtime to boot. Run it under `--browser webkit`
// and the engine is WebKit — not `WKWebView`, but the same JavaScriptCore and
// wasm implementation the app will end up on, which is as close as this gets
// without a device.
//
// Playwright is installed into this directory on demand rather than vendored,
// and lives here rather than beside the page because ios/ContainerRuntime/ is
// copied wholesale into the app bundle.
//
// Usage: node container-runtime-boot-smoke.mjs <htdocs-dir>
//          [--browser chromium|webkit] [--arch aarch64] [--timeout 1200]

import { createServer } from "node:http";
import { createReadStream } from "node:fs";
import { stat } from "node:fs/promises";
import { extname, join, normalize, resolve } from "node:path";
import * as playwright from "playwright";

const args = process.argv.slice(2);
const root = resolve(args[0] ?? ".");
const arch = valueOf("--arch") ?? "aarch64";
const browserName = valueOf("--browser") ?? "chromium";
const timeoutSeconds = Number(valueOf("--timeout") ?? 1200);

if (!playwright[browserName]) {
  console.error(`unknown browser: ${browserName}`);
  process.exit(2);
}

function valueOf(flag) {
  const index = args.indexOf(flag);
  return index === -1 ? undefined : args[index + 1];
}

const CONTENT_TYPES = {
  ".css": "text/css; charset=utf-8",
  ".data": "application/octet-stream",
  ".html": "text/html; charset=utf-8",
  ".js": "text/javascript; charset=utf-8",
  ".json": "application/json; charset=utf-8",
  ".mjs": "text/javascript; charset=utf-8",
  ".wasm": "application/wasm",
};

// The same headers the iOS loopback server sends. Without them the page is not
// cross-origin isolated, SharedArrayBuffer is missing, and QEMU's threads
// cannot start — which is the failure mode this test exists to catch.
const ISOLATION_HEADERS = {
  "Cross-Origin-Opener-Policy": "same-origin",
  "Cross-Origin-Embedder-Policy": "require-corp",
  "Cross-Origin-Resource-Policy": "same-origin",
};

const server = createServer(async (request, response) => {
  const requested = new URL(request.url, "http://127.0.0.1").pathname;
  const relative = normalize(requested === "/" ? "/index.html" : requested).replace(/^(\.\.[/\\])+/, "");
  const file = join(root, relative);

  try {
    const info = await stat(file);
    if (!info.isFile()) throw new Error("not a file");
    response.writeHead(200, {
      ...ISOLATION_HEADERS,
      "Content-Type": CONTENT_TYPES[extname(file)] ?? "application/octet-stream",
      "Content-Length": info.size,
    });
    createReadStream(file).pipe(response);
  } catch {
    response.writeHead(404, ISOLATION_HEADERS);
    response.end("not found\n");
  }
});

await new Promise((done) => server.listen(0, "127.0.0.1", done));
const origin = `http://127.0.0.1:${server.address().port}`;
console.log(`serving ${root} at ${origin}`);

console.log(`browser: ${browserName}`);
const browser = await playwright[browserName].launch();
const page = await browser.newPage();
// The page mirrors every guest line to the console for the Swift bridge's
// benefit; skip those, since this script echoes the terminal itself.
page.on("console", (message) => {
  const text = message.text();
  if (!text.startsWith("containerLab {kind: output")) console.log(`[page] ${text}`);
});
page.on("pageerror", (error) => console.log(`[page error] ${error}`));

// Shared across waits so the second one picks up where the first left off.
let echoedLines = 0;
let failure = null;
try {
  await page.goto(origin, { waitUntil: "domcontentloaded" });

  const isolated = await page.evaluate(() => self.crossOriginIsolated === true);
  if (!isolated) throw new Error("page is not cross-origin isolated");

  await waitForGuest(/\/ # ?$/m, "a shell prompt");
  // The prompt is drawn before the guest's TTY is reading, so give it a beat
  // rather than burning a retry on a command nobody is listening for.
  await new Promise((done) => setTimeout(done, 3000));
  await askGuest("uname -sm", new RegExp(`Linux ${arch}`), `"Linux ${arch}"`);

  console.log(`\nalpine booted and answered as Linux ${arch}.`);
} catch (error) {
  failure = error;
  console.error(`\nboot smoke test failed: ${error.message}`);
  console.error("--- terminal buffer ---");
  console.error(await readTerminal().catch(() => "(terminal unreadable)"));
} finally {
  await browser.close();
  server.close();
}

process.exit(failure ? 1 : 0);

/// Types a command at the guest and waits for its answer.
///
/// Pastes rather than synthesising keystrokes, so the test does not depend on
/// where focus happens to be — and retries, because a command sent the instant
/// the prompt appears is occasionally swallowed before the guest's TTY is
/// listening.
async function askGuest(command, pattern, description) {
  const attempts = 3;
  for (let attempt = 1; attempt <= attempts; attempt++) {
    await page.evaluate((line) => window.containerLabTerminal.paste(line), `${command}\r`);
    try {
      await waitForGuest(pattern, description, Math.max(30, timeoutSeconds / attempts));
      return;
    } catch (error) {
      if (attempt === attempts) throw error;
      console.log(`\n(no answer to "${command}"; retrying ${attempt + 1}/${attempts})`);
    }
  }
}

/// Everything the guest has printed, scrollback included.
async function readTerminal() {
  return page.evaluate(() => {
    const terminal = window.containerLabTerminal;
    if (!terminal) return "";
    const buffer = terminal.buffer.active;
    const lines = [];
    for (let i = 0; i < buffer.length; i++) {
      lines.push(buffer.getLine(i)?.translateToString(true) ?? "");
    }
    return lines.join("\n").replace(/\n+$/, "");
  });
}

/// Polls the guest's output until `pattern` shows up, echoing new lines so the
/// CI log shows boot progress rather than a silent twenty-minute wait.
async function waitForGuest(pattern, description, seconds = timeoutSeconds) {
  const deadline = Date.now() + seconds * 1000;

  while (Date.now() < deadline) {
    const text = await readTerminal();
    // Echo whole lines only: the last one is still being written, and the
    // shell rewrites it as characters are echoed back.
    const lines = text.split("\n");
    // Scrollback eventually drops the oldest lines, so the buffer can shrink.
    if (lines.length - 1 < echoedLines) echoedLines = lines.length - 1;
    while (echoedLines < lines.length - 1) console.log(lines[echoedLines++]);

    if (pattern.test(text)) return;
    await new Promise((done) => setTimeout(done, 500));
  }

  throw new Error(`timed out after ${seconds}s waiting for ${description}`);
}
