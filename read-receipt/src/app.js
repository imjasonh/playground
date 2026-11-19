// Wires the compose form, the word-by-word reader, and receipt links to the
// page.

import {renderMarkdown} from './markdown.js';
import {
  MAX_WPM,
  Reader,
  formatDuration,
  isAdvanceKey,
  withinSpeedLimit,
  wordsPerMinute,
} from './reader.js';
import {
  MAX_LINK_LENGTH,
  longestLink,
  readReceipt,
  receiptHash,
} from './receipt.js';
import {wrapWords} from './words.js';

/**
 * @param {string} id
 * @return {!HTMLElement}
 */
function byId(id) {
  const element = document.getElementById(id);
  if (!element) throw new Error(`missing #${id}`);
  return element;
}

const compose = /** @type {!HTMLFormElement} */ (byId('compose'));
const source = /** @type {!HTMLTextAreaElement} */ (byId('source'));
const composeError = byId('compose-error');
const toolbar = byId('toolbar');
const progress = /** @type {!HTMLProgressElement} */ (byId('progress'));
const count = byId('count');
const hint = byId('hint');
const slow = byId('slow');
const banner = byId('banner');
const doc = byId('doc');
const done = byId('done');
const doneTitle = byId('done-title');
const doneSummary = byId('done-summary');
const link = /** @type {!HTMLInputElement} */ (byId('link'));
const copyButton = byId('copy');
const copyTip = byId('copy-tip');
const shareButton = byId('share');
const receiptActions = byId('receipt-actions');

/** The Markdown on screen. */
let markdown = '';
/** @type {?Reader} Set while the reader is stepping through a doc. */
let reader = null;
/** @type {!Array<!Array<!HTMLSpanElement>>} Each word's spans. */
let words = [];

/**
 * @param {number} index
 * @param {string} className
 * @param {boolean} on
 */
function markWord(index, className, on) {
  for (const span of words[index]) span.classList.toggle(className, on);
}

/** @param {'compose'|'reading'|'receipt'} view */
function show(view) {
  compose.hidden = view !== 'compose';
  toolbar.hidden = view !== 'reading';
  done.hidden = true;
  slow.textContent = '';
  doc.hidden = view === 'compose';
  banner.hidden = view !== 'receipt';
  receiptActions.hidden = view !== 'receipt';
  doc.classList.toggle('reading', view === 'reading');
}

/** @param {string} message Empty to clear. */
function showComposeError(message) {
  composeError.textContent = message;
  composeError.hidden = !message;
}

/** Drops a receipt fragment from the address bar without a navigation. */
function clearHash() {
  if (location.hash) {
    history.replaceState(null, '', location.pathname + location.search);
  }
}

function updateProgress() {
  if (!reader) return;
  progress.max = reader.total;
  progress.value = reader.index;
  count.textContent =
    `${reader.index.toLocaleString()} of ` +
    `${reader.total.toLocaleString()} words`;
  hint.hidden = reader.done || Boolean(slow.textContent);
}

/**
 * Scrolls `word` back to the middle of the screen below the toolbar once it
 * drifts a tenth of the screen away, so the page moves every few lines and
 * not on every word.
 * @param {!HTMLElement} word
 */
function keepInView(word) {
  const rect = word.getBoundingClientRect();
  const height = window.innerHeight;
  const top = Math.max(0, toolbar.getBoundingClientRect().bottom);
  const drift = (rect.top + rect.bottom) / 2 - (top + height) / 2;
  if (Math.abs(drift) > height * 0.1) window.scrollBy({top: drift});
  // Code blocks and tables scroll sideways on their own.
  const box = word.closest('pre, table');
  if (box) {
    const edges = box.getBoundingClientRect();
    if (rect.left < edges.left || rect.right > edges.right) {
      box.scrollLeft += rect.left - edges.left - edges.width / 2;
    }
  }
}

/** @return {string} This page's address without the fragment. */
function pageAddress() {
  return location.origin + location.pathname + location.search;
}

/** @param {string} text */
async function startReading(text) {
  reader = null;
  const length = await longestLink(pageAddress(), text);
  if (length > MAX_LINK_LENGTH) {
    show('compose');
    showComposeError(
      `This doc is too long for a receipt link. Its link would be about ` +
        `${length.toLocaleString()} characters, and the limit is ` +
        `${MAX_LINK_LENGTH.toLocaleString()}. Ask your agent to make it ` +
        'shorter?',
    );
    return;
  }
  markdown = text;
  renderMarkdown(doc, text);
  words = wrapWords(doc);
  if (!words.length) {
    reader = null;
    show('compose');
    showComposeError('That doc has no words to read.');
    return;
  }
  showComposeError('');
  clearHash();
  reader = new Reader(words.length);
  show('reading');
  markWord(0, 'current', true);
  updateProgress();
  window.scrollTo({top: 0});
}

function advance() {
  if (!reader) return;
  const previous = reader.index;
  if (!reader.advance()) {
    slowDown();
    return;
  }
  markWord(previous, 'current', false);
  markWord(previous, 'read', true);
  updateProgress();
  if (reader.done) {
    void finish(reader);
    return;
  }
  markWord(reader.index, 'current', true);
  keepInView(words[reader.index][0]);
}

/** Flashes the current word. */
function nudge() {
  if (!reader || reader.done) return;
  markWord(reader.index, 'nudge', false);
  void doc.offsetWidth;
  markWord(reader.index, 'nudge', true);
  keepInView(words[reader.index][0]);
}

/** @type {number|undefined} */
let slowTimer;

/** Flashes the current word and says why a step was refused. */
function slowDown() {
  if (!reader || reader.done) return;
  nudge();
  slow.textContent = `Slow down. The limit is ${MAX_WPM} words a minute.`;
  updateProgress();
  clearTimeout(slowTimer);
  slowTimer = setTimeout(() => {
    slow.textContent = '';
    updateProgress();
  }, 2000);
}

const dateFormat = new Intl.DateTimeFormat(undefined, {
  dateStyle: 'medium',
  timeStyle: 'short',
});

/**
 * @param {number} total
 * @param {number} seconds
 * @param {?Date} finished
 * @return {string} Like "all 192 words in 47s (245 words a minute), finishing
 *     Nov 18, 2026, 9:58 PM", in the viewer's time zone.
 */
function describeReading(total, seconds, finished) {
  let read = `all ${total.toLocaleString()} words in ${formatDuration(seconds)}`;
  const wpm = wordsPerMinute(total, seconds);
  if (wpm !== null) read += ` (${wpm.toLocaleString()} words a minute)`;
  return finished ? `${read}, finishing ${dateFormat.format(finished)}` : read;
}

/**
 * @param {number} total
 * @param {{seconds: number, finished: ?Date, verified: boolean}} receipt
 * @return {string} What the banner says about `receipt`.
 */
function describeReceipt(total, receipt) {
  if (!receipt.verified) {
    return "This receipt doesn't match the doc. The doc or the times in the " +
      'link changed after the receipt was made.';
  }
  if (!withinSpeedLimit(total, receipt.seconds)) {
    return `This receipt is too fast to be real: ${total.toLocaleString()} ` +
      `words in ${formatDuration(receipt.seconds)} is over the limit of ` +
      `${MAX_WPM} words a minute.`;
  }
  return 'Receipt checks out. The person who sent you this clicked through ' +
    `${describeReading(total, receipt.seconds, receipt.finished)}.`;
}

/** @param {!Reader} finished */
async function finish(finished) {
  const seconds = finished.seconds;
  const end = Math.floor((finished.finishedAt ?? Date.now()) / 1000);
  const url = new URL(location.href);
  url.hash = await receiptHash(markdown, seconds, end);
  if (reader !== finished) return;
  doc.classList.remove('reading');
  link.value = url.href;
  doneSummary.textContent =
    `You clicked through ` +
    `${describeReading(finished.total, seconds, new Date(end * 1000))}. ` +
    'Whoever opens this link sees the doc, your time, and when you finished.';
  history.replaceState(null, '', url);
  done.hidden = false;
  window.scrollTo({top: 0});
  doneTitle.focus({preventScroll: true});
}

/**
 * Shows the doc in the address bar's receipt, or the compose form when there
 * is none.
 */
async function route() {
  reader = null;
  let receipt;
  try {
    receipt = await readReceipt(location.hash);
  } catch {
    clearHash();
    show('compose');
    showComposeError("That receipt link is damaged, so its doc can't be shown.");
    return;
  }
  if (!receipt) {
    show('compose');
    source.focus();
    return;
  }
  markdown = receipt.markdown;
  renderMarkdown(doc, markdown);
  const total = wrapWords(doc).length;
  banner.classList.toggle(
    'bad',
    !receipt.verified || !withinSpeedLimit(total, receipt.seconds),
  );
  banner.textContent = describeReceipt(total, receipt);
  show('receipt');
  window.scrollTo({top: 0});
}

compose.addEventListener('submit', (event) => {
  event.preventDefault();
  void startReading(source.value);
});

source.addEventListener('input', () => showComposeError(''));

byId('edit').addEventListener('click', () => {
  reader = null;
  clearHash();
  source.value = markdown;
  show('compose');
  source.focus();
});

byId('read-yourself').addEventListener('click', () => {
  source.value = markdown;
  void startReading(markdown);
});

// A click or tap anywhere on the page moves to the next word.
document.addEventListener('click', (event) => {
  if (!reader || reader.done) return;
  const target = /** @type {!Element} */ (event.target);
  if (target.closest('button, input, textarea, select')) return;
  if (target.closest('a')) {
    if (!doc.contains(target)) return;
    // Links in the doc only open once it's read.
    event.preventDefault();
  }
  advance();
});

document.addEventListener('keydown', (event) => {
  if (!reader || reader.done) return;
  if (event.key !== ' ' && event.key !== 'ArrowRight') return;
  const target = /** @type {!Element} */ (event.target);
  if (target.closest?.('button, input, textarea, select, [contenteditable]')) {
    return;
  }
  if (event.altKey || event.ctrlKey || event.metaKey || event.shiftKey) return;
  // Held keys still don't scroll the page, but only fresh presses count.
  event.preventDefault();
  if (isAdvanceKey(event)) advance();
});

doc.addEventListener('animationend', (event) => {
  /** @type {!Element} */ (event.target).classList.remove('nudge');
});

/** @type {number|undefined} */
let copyTimer;

/** @param {boolean} ok */
function reportCopy(ok) {
  clearTimeout(copyTimer);
  copyTip.textContent = '';
  requestAnimationFrame(() => {
    copyTip.textContent = ok ? 'Copied' : 'Copy failed';
  });
  copyTimer = setTimeout(() => {
    copyTip.textContent = '';
  }, 2000);
}

copyButton.addEventListener('click', async () => {
  try {
    await navigator.clipboard.writeText(link.value);
    reportCopy(true);
  } catch {
    link.select();
    reportCopy(false);
  }
});

if ('share' in navigator) {
  shareButton.hidden = false;
  shareButton.addEventListener('click', async () => {
    try {
      await navigator.share({title: document.title, url: link.value});
    } catch {
      // The user closed the share sheet.
    }
  });
}

window.addEventListener('hashchange', () => void route());
void route();
