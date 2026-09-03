#!/usr/bin/env node
// Playwright runner for the OfflineAudioContext HRTF proof.
import { createServer } from 'node:http';
import { readFileSync, existsSync } from 'node:fs';
import { extname, join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium } from 'playwright';

const root = join(dirname(fileURLToPath(import.meta.url)), '..');
const TYPES = {
  '.html': 'text/html',
  '.js': 'text/javascript',
  '.mjs': 'text/javascript',
  '.css': 'text/css',
  '.json': 'application/json',
};

const server = createServer((req, res) => {
  const rel = decodeURIComponent((req.url || '/').split('?')[0]);
  const path = join(root, rel);
  if (!path.startsWith(root) || !existsSync(path)) {
    res.writeHead(404);
    res.end('not found');
    return;
  }
  res.writeHead(200, { 'Content-Type': TYPES[extname(path)] || 'application/octet-stream' });
  res.end(readFileSync(path));
});

await new Promise((resolve) => server.listen(0, '127.0.0.1', resolve));
const { port } = server.address();

const browser = await chromium.launch();
const page = await browser.newPage();
const errors = [];
page.on('pageerror', (e) => errors.push(String(e)));
page.on('console', (msg) => {
  if (msg.type() === 'error') errors.push(msg.text());
});

await page.goto(`http://127.0.0.1:${port}/tests/hrtf-harness.html`, {
  waitUntil: 'networkidle',
});
await page.waitForFunction(() => document.getElementById('out')?.textContent?.startsWith('HRTF_PROOF='), {
  timeout: 15000,
});
const text = await page.textContent('#out');
await browser.close();
server.close();

if (!text?.startsWith('HRTF_PROOF=')) {
  console.error(JSON.stringify({ pass: false, reason: 'no proof marker', errors }));
  process.exit(1);
}
const verdict = JSON.parse(text.slice('HRTF_PROOF='.length));
if (errors.length) verdict.pageErrors = errors;
console.log(JSON.stringify(verdict, null, 2));
process.exit(verdict.pass ? 0 : 1);
