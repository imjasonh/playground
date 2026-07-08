#!/usr/bin/env node
/**
 * Local API proxy for the Xeneon Cursor HUD.
 *
 * - Serves the static UI from ../ui
 * - Proxies /api/* to Cursor Cloud Agents API with CURSOR_API_KEY
 * - Supports --mock for offline demos
 */

import http from 'node:http';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { createCursorProxyHandler } from './handler.mjs';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const root = path.resolve(__dirname, '..');
const uiRoot = path.join(root, 'ui');

const mock = process.argv.includes('--mock') || process.env.MOCK === '1';
const host = process.env.HOST || '127.0.0.1';
const port = Number(process.env.PORT || 8787);
const apiBase = process.env.CURSOR_API_BASE || 'https://api.cursor.com';
const apiKey = process.env.CURSOR_API_KEY || '';
const version = readVersion();

loadDotEnv(path.join(root, '.env'));

const handler = createCursorProxyHandler({
  apiBase: process.env.CURSOR_API_BASE || apiBase,
  apiKey: process.env.CURSOR_API_KEY || apiKey,
  mock: mock || (!(process.env.CURSOR_API_KEY || apiKey) && process.argv.includes('--mock')),
  version,
  forceMock: mock,
});

const server = http.createServer(async (req, res) => {
  try {
    const url = new URL(req.url || '/', `http://${host}:${port}`);

    if (url.pathname === '/' || url.pathname.startsWith('/css/') || url.pathname.startsWith('/js/')) {
      return serveStatic(url.pathname === '/' ? '/index.html' : url.pathname, res);
    }

    if (url.pathname.startsWith('/api/')) {
      return handler(req, res, url);
    }

    res.writeHead(404, { 'Content-Type': 'application/json' });
    res.end(JSON.stringify({ error: 'Not found' }));
  } catch (err) {
    res.writeHead(500, { 'Content-Type': 'application/json' });
    res.end(JSON.stringify({ error: 'Internal error', message: String(err?.message || err) }));
  }
});

server.listen(port, host, () => {
  const mode = handler.mode();
  console.log(`Xeneon Cursor proxy listening on http://${host}:${port} (${mode})`);
  if (mode === 'live' && !(process.env.CURSOR_API_KEY || apiKey)) {
    console.warn('Warning: CURSOR_API_KEY is not set. Use --mock or set the key.');
  }
});

function readVersion() {
  try {
    return fs.readFileSync(path.join(root, 'VERSION'), 'utf8').trim();
  } catch {
    return '0.0.0';
  }
}

function loadDotEnv(file) {
  if (!fs.existsSync(file)) return;
  const text = fs.readFileSync(file, 'utf8');
  for (const line of text.split('\n')) {
    const trimmed = line.trim();
    if (!trimmed || trimmed.startsWith('#')) continue;
    const eq = trimmed.indexOf('=');
    if (eq < 0) continue;
    const key = trimmed.slice(0, eq).trim();
    let value = trimmed.slice(eq + 1).trim();
    if (
      (value.startsWith('"') && value.endsWith('"')) ||
      (value.startsWith("'") && value.endsWith("'"))
    ) {
      value = value.slice(1, -1);
    }
    if (!(key in process.env)) process.env[key] = value;
  }
}

function contentType(filePath) {
  if (filePath.endsWith('.html')) return 'text/html; charset=utf-8';
  if (filePath.endsWith('.css')) return 'text/css; charset=utf-8';
  if (filePath.endsWith('.js')) return 'text/javascript; charset=utf-8';
  if (filePath.endsWith('.svg')) return 'image/svg+xml';
  if (filePath.endsWith('.json')) return 'application/json';
  return 'application/octet-stream';
}

function serveStatic(pathname, res) {
  const safe = path.normalize(pathname).replace(/^(\.\.[/\\])+/, '');
  const filePath = path.join(uiRoot, safe);
  if (!filePath.startsWith(uiRoot)) {
    res.writeHead(403);
    res.end('Forbidden');
    return;
  }
  if (!fs.existsSync(filePath) || fs.statSync(filePath).isDirectory()) {
    res.writeHead(404);
    res.end('Not found');
    return;
  }
  const data = fs.readFileSync(filePath);
  res.writeHead(200, { 'Content-Type': contentType(filePath) });
  res.end(data);
}
