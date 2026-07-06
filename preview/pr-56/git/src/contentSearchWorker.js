/**
 * Content-search worker: decodes file bytes and scans them for the active query
 * off the main thread, so grepping a whole repo doesn't block typing/scrolling.
 * The pattern/scan logic is shared with the main thread (contentSearch.js).
 *
 * Protocol — main → worker:
 *   { type: 'begin', id, query, options }      compile the matcher for a search
 *   { type: 'file', id, reqId, path, bytes, limits }
 * worker → main:
 *   { type: 'matches', id, reqId, path, matches }
 *
 * `id` identifies a search; the matcher is compiled once on `begin` and reused
 * across that search's files. A `file` for a superseded search still gets a
 * (empty) reply, so the client's per-file promise never hangs.
 *
 * Loaded as a module worker so it can `import` directly with no build step.
 */
import { buildPattern, searchContent } from './contentSearch.js';

const decoder = new TextDecoder('utf-8', { fatal: false });
let current = { id: -1, re: null };

self.onmessage = (event) => {
  const msg = event.data || {};
  if (msg.type === 'begin') {
    const { re } = buildPattern(msg.query, msg.options || {});
    current = { id: msg.id, re };
    return;
  }
  if (msg.type === 'file') {
    // Only scan if this file belongs to the active search; otherwise reply empty
    // so the awaiting caller resolves rather than leaking.
    const re = msg.id === current.id ? current.re : null;
    const matches = re ? searchContent(decoder.decode(msg.bytes), re, msg.limits) : [];
    self.postMessage({ type: 'matches', id: msg.id, reqId: msg.reqId, path: msg.path, matches });
  }
};
