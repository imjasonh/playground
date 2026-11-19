// Wires the compose form, the word-by-word reader, and receipt links to the
// page.

import {renderMarkdown} from './markdown.js';
import {Reader, formatDuration, isAdvanceKey} from './reader.js';
import {readReceipt, receiptHash} from './receipt.js';
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
/** @type {!Map<!Element, number>} The word index of each span. */
let wordOf = new Map();

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
  hint.hidden = reader.done;
}

/**
 * Scrolls `word` toward the middle of the viewport once it leaves the middle
 * half, so the page doesn't move on every word.
 * @param {!HTMLElement} word
 */
function keepInView(word) {
  const rect = word.getBoundingClientRect();
  const height = window.innerHeight;
  if (rect.top < height * 0.25 || rect.bottom > height * 0.75) {
    word.scrollIntoView({block: 'center', inline: 'nearest'});
  } else {
    // Words inside a code block can still be off to the side.
    word.scrollIntoView({block: 'nearest', inline: 'nearest'});
  }
}

/** @param {string} text */
function startReading(text) {
  markdown = text;
  renderMarkdown(doc, text);
  words = wrapWords(doc);
  wordOf = new Map(
    words.flatMap((spans, index) => spans.map((span) => [span, index])),
  );
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
  if (!reader.advance()) return;
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

/** Flashes the current word after a click on some other word. */
function nudge() {
  if (!reader || reader.done) return;
  markWord(reader.index, 'nudge', false);
  void doc.offsetWidth;
  markWord(reader.index, 'nudge', true);
  keepInView(words[reader.index][0]);
}

const dateFormat = new Intl.DateTimeFormat(undefined, {
  dateStyle: 'medium',
  timeStyle: 'short',
});

/**
 * @param {number} total
 * @param {number} seconds
 * @param {?Date} finished
 * @return {string} Like "all 192 words in 53s, finishing Nov 18, 2026, 9:58
 *     PM", in the viewer's time zone.
 */
function describeReading(total, seconds, finished) {
  const read = `all ${total.toLocaleString()} words in ${formatDuration(seconds)}`;
  return finished ? `${read}, finishing ${dateFormat.format(finished)}` : read;
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
  banner.classList.toggle('bad', !receipt.verified);
  banner.textContent = receipt.verified ?
    'Receipt checks out. The person who sent you this clicked through ' +
      `${describeReading(total, receipt.seconds, receipt.finished)}.` :
    "This receipt doesn't match the doc. The doc or the times in the link " +
      'changed after the receipt was made.';
  show('receipt');
  window.scrollTo({top: 0});
}

compose.addEventListener('submit', (event) => {
  event.preventDefault();
  startReading(source.value);
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
  startReading(markdown);
});

doc.addEventListener('click', (event) => {
  if (!reader || reader.done) return;
  const target = /** @type {!Element} */ (event.target);
  // Links in the doc only open once it's read.
  if (target.closest('a')) event.preventDefault();
  const span = target.closest('.word');
  if (span && wordOf.get(span) === reader.index) {
    advance();
  } else {
    nudge();
  }
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
