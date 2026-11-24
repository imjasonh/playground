// Wires the compose form, the word-by-word reader, and receipt links to the
// page.

import {renderMarkdown} from './markdown.js';
import {
  MAX_WPM,
  Reader,
  formatDuration,
  isStepKey,
  withinSpeedLimit,
  wordsPerMinute,
} from './reader.js';
import {
  MAX_LINK_LENGTH,
  longestLink,
  readReceipt,
  receiptFragment,
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

/**
 * @param {?EventTarget} target Not always an element: an event dispatched on
 *     the document targets the document.
 * @return {boolean} Whether `target` keeps its own clicks and keys.
 */
function isControl(target) {
  return target instanceof Element &&
    target.closest('button, input, textarea, select, [contenteditable]') !==
      null;
}

/** The Markdown on screen. */
let markdown = '';
/** @type {?Reader} Set only in the reading view. */
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
  if (view !== 'reading') reader = null;
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

/** @param {!Reader} current */
function updateProgress(current) {
  progress.max = current.total;
  progress.value = current.index;
  count.textContent =
    `${current.index.toLocaleString()} of ` +
    `${current.total.toLocaleString()} words`;
  hint.hidden = current.done;
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
    show('compose');
    showComposeError('That doc has no words to read.');
    return;
  }
  showComposeError('');
  clearHash();
  reader = new Reader(words.length);
  show('reading');
  markWord(0, 'current', true);
  updateProgress(reader);
  window.scrollTo({top: 0});
}

/** @param {!Reader} current */
function advance(current) {
  const previous = current.index;
  if (!current.advance()) {
    slowDown(current.index);
    return;
  }
  markWord(previous, 'current', false);
  markWord(previous, 'read', true);
  updateProgress(current);
  if (current.done) {
    void finish(current);
    return;
  }
  markWord(current.index, 'current', true);
  keepInView(words[current.index][0]);
}

/** @type {number|undefined} */
let slowTimer;

/**
 * Flashes the current word and says why a step was refused.
 * @param {number} index
 */
function slowDown(index) {
  markWord(index, 'nudge', false);
  // Restarts the flash when it's still running.
  void doc.offsetWidth;
  markWord(index, 'nudge', true);
  keepInView(words[index][0]);
  slow.textContent = `Slow down. The limit is ${MAX_WPM} words a minute.`;
  clearTimeout(slowTimer);
  slowTimer = setTimeout(() => {
    slow.textContent = '';
  }, 2000);
}

const dateFormat = new Intl.DateTimeFormat(undefined, {
  dateStyle: 'medium',
  timeStyle: 'short',
});

/**
 * @param {number} total
 * @param {!Reading} reading
 * @return {string} Like "all 192 words in 47s (245 words a minute), finishing
 *     Nov 18, 2026, 9:58 PM", in the viewer's time zone.
 */
function describeReading(total, {seconds, finished}) {
  let read = `all ${total.toLocaleString()} words in ${formatDuration(seconds)}`;
  const wpm = wordsPerMinute(total, seconds);
  if (wpm !== null) read += ` (${wpm.toLocaleString()} words a minute)`;
  return finished ? `${read}, finishing ${dateFormat.format(finished)}` : read;
}

/**
 * @param {number} total
 * @param {?Reading} reading Null when the receipt doesn't match its doc.
 * @return {{ok: boolean, message: string}} Whether the receipt holds up, and
 *     what the banner says about it.
 */
function judgeReceipt(total, reading) {
  if (!reading) {
    return {
      ok: false,
      message: "This receipt doesn't match the doc. The doc or the times in " +
        'the link changed after the receipt was made.',
    };
  }
  if (!withinSpeedLimit(total, reading.seconds)) {
    return {
      ok: false,
      message: `This receipt is too fast to be real: ` +
        `${total.toLocaleString()} words in ` +
        `${formatDuration(reading.seconds)} is over the limit of ` +
        `${MAX_WPM} words a minute.`,
    };
  }
  return {
    ok: true,
    message: 'Receipt checks out. The person who sent you this clicked ' +
      `through ${describeReading(total, reading)}.`,
  };
}

/** @param {!Reader} finished */
async function finish(finished) {
  const seconds = finished.seconds;
  const end = Math.floor(/** @type {number} */ (finished.finishedAt) / 1000);
  const fragment = await receiptFragment(markdown, seconds, end);
  if (reader !== finished) return;
  const href = `${pageAddress()}#${fragment}`;
  doc.classList.remove('reading');
  link.value = href;
  const reading = {seconds, finished: new Date(end * 1000)};
  doneSummary.textContent =
    `You clicked through ${describeReading(finished.total, reading)}. ` +
    'Whoever opens this link sees the doc, your time, and when you finished.';
  history.replaceState(null, '', href);
  done.hidden = false;
  window.scrollTo({top: 0});
  doneTitle.focus({preventScroll: true});
}

/**
 * Shows the doc in the address bar's receipt, or the compose form when there
 * is none.
 */
async function route() {
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
  const {ok, message} = judgeReceipt(wrapWords(doc).length, receipt.reading);
  banner.classList.toggle('bad', !ok);
  banner.textContent = message;
  show('receipt');
  window.scrollTo({top: 0});
}

compose.addEventListener('submit', (event) => {
  event.preventDefault();
  void startReading(source.value);
});

source.addEventListener('input', () => showComposeError(''));

byId('edit').addEventListener('click', () => {
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
  if (!reader || reader.done || isControl(event.target)) return;
  const target = event.target;
  if (target instanceof Element && target.closest('a')) {
    if (!doc.contains(target)) return;
    // Links in the doc only open once it's read.
    event.preventDefault();
  }
  advance(reader);
});

document.addEventListener('keydown', (event) => {
  if (!reader || reader.done || !isStepKey(event)) return;
  if (isControl(event.target)) return;
  // Held keys still don't scroll the page, but only fresh presses count.
  event.preventDefault();
  if (!event.repeat) advance(reader);
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
