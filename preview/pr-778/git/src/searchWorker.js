/**
 * Search worker: owns the fuzzy file index so building it (lowercasing every
 * path) and scanning it on every keystroke happens off the main thread. On a
 * huge repo this is the work that used to jank typing in the file finder.
 *
 * The pure matching/index logic is shared with the main thread (fuzzy.js); this
 * module is just the message-pump that holds the corpus between queries.
 *
 * Protocol — main → worker:
 *   { type: 'setFiles', epoch:number, files:string[] }   replace the corpus
 *   { type: 'query', id:number, query:string, limit?:number }
 * worker → main:
 *   { type: 'result', id:number, epoch:number, results:Result[] }
 *
 * `epoch` lets the main thread drop a result that was computed against a corpus
 * it has since replaced (messages are processed in order, so a query always sees
 * the latest setFiles that preceded it).
 *
 * Loaded as a module worker (`new Worker(url, { type: 'module' })`) so it can
 * `import` directly with no build step, matching the rest of the app.
 */
import { buildIndex, fuzzyFilterIndex } from './fuzzy.js';

let index = buildIndex([]);
let epoch = 0;

self.onmessage = (event) => {
  const msg = event.data || {};
  if (msg.type === 'setFiles') {
    epoch = msg.epoch;
    index = buildIndex(msg.files || []);
    return;
  }
  if (msg.type === 'query') {
    const results = fuzzyFilterIndex(msg.query, index, { limit: msg.limit });
    self.postMessage({ type: 'result', id: msg.id, epoch, results });
  }
};
