/**
 * Content-search overlay: a modal grep across file *contents* (as opposed to the
 * command palette, which matches file *names*). Results stream in grouped by file
 * as the worker-backed client (see contentSearchClient.js) scans, and each match
 * line opens the file at that line — reusing the viewer's line-targeting from the
 * deep-link work.
 *
 * Owns its own UI state and restores focus to its trigger on close, mirroring the
 * command palette.
 */
import { el, debounce } from './dom.js';

const DEBOUNCE_MS = 180;
// Cap rendered rows so a broad query can't build an enormous DOM (the client also
// caps total matches; this is the view-side guard).
const MAX_RENDERED = 500;

/**
 * @param {{state: object, dom: Record<string, HTMLElement>, contentSearch: object, openFile: Function}} ctx
 */
export function createContentSearch(ctx) {
  const { state, dom } = ctx;
  let returnFocus = null;
  let activeSignal = null; // { aborted } for the in-flight search
  let rows = []; // flat, navigable list of { el, path, line }
  let activeIndex = -1;
  let rendered = 0;
  let truncatedDom = false;

  const runDebounced = debounce(run, DEBOUNCE_MS);

  dom.contentSearchInput.addEventListener('input', runDebounced);
  dom.contentSearchInput.addEventListener('keydown', onKey);
  dom.csRegex.addEventListener('change', run);
  dom.csCase.addEventListener('change', run);
  dom.contentSearch.addEventListener('click', (event) => {
    if (event.target === dom.contentSearch) close();
  });

  function isOpen() {
    return !dom.contentSearch.hidden;
  }

  function open() {
    if (!state.source) return;
    returnFocus = document.activeElement;
    dom.contentSearch.hidden = false;
    dom.contentSearchInput.focus();
    dom.contentSearchInput.select();
    run(); // re-run any retained query so reopening shows current results
  }

  function close() {
    if (activeSignal) activeSignal.aborted = true;
    const wasOpen = isOpen();
    dom.contentSearch.hidden = true;
    if (
      wasOpen &&
      returnFocus &&
      typeof returnFocus.focus === 'function' &&
      document.contains(returnFocus)
    ) {
      returnFocus.focus();
    }
    returnFocus = null;
  }

  function queryOptions() {
    return { regex: dom.csRegex.checked, caseSensitive: dom.csCase.checked };
  }

  function resetResults() {
    rows = [];
    activeIndex = -1;
    rendered = 0;
    truncatedDom = false;
    dom.contentSearchResults.replaceChildren();
    dom.contentSearchEmpty.hidden = true;
  }

  async function run() {
    if (!state.source) return;
    // Supersede any search still in flight.
    if (activeSignal) activeSignal.aborted = true;
    const signal = { aborted: false };
    activeSignal = signal;

    const query = dom.contentSearchInput.value;
    resetResults();
    if (!query.trim()) {
      setStatus('');
      return;
    }
    setStatus('Searching…');

    const summary = await ctx.contentSearch.search(state.files, query, queryOptions(), {
      readFile: (path) => state.source.readFile(path),
      onResult: (result) => {
        if (!signal.aborted) appendResult(result);
      },
      onProgress: (processed, total) => {
        if (!signal.aborted) setStatus(`Searching… ${processed}/${total}`);
      },
      signal,
    });

    if (signal.aborted) return;
    showSummary(summary);
  }

  function showSummary(summary) {
    if (summary.error) {
      setStatus(`Invalid pattern: ${summary.error}`, true);
      return;
    }
    if (summary.matches === 0) {
      setStatus('');
      dom.contentSearchEmpty.hidden = false;
      return;
    }
    const files = `${summary.files} file${summary.files === 1 ? '' : 's'}`;
    const hits = `${summary.matches} match${summary.matches === 1 ? '' : 'es'}`;
    const capped = summary.truncated || truncatedDom ? ' · showing first results' : '';
    setStatus(`${hits} in ${files}${capped}`);
  }

  function setStatus(text, isError = false) {
    dom.contentSearchStatus.textContent = text;
    dom.contentSearchStatus.classList.toggle('error', isError);
  }

  function appendResult({ path, matches }) {
    if (rendered >= MAX_RENDERED) {
      truncatedDom = true;
      return;
    }
    const group = el('div', 'cs-file');
    const head = el('button', 'cs-file-head');
    head.type = 'button';
    head.appendChild(el('span', 'cs-file-path', path));
    head.appendChild(el('span', 'cs-file-count', String(matches.length)));
    head.addEventListener('click', () => openAt(path, matches[0].line));
    group.appendChild(head);

    for (const match of matches) {
      if (rendered >= MAX_RENDERED) {
        truncatedDom = true;
        break;
      }
      const row = el('button', 'cs-line');
      row.type = 'button';
      row.appendChild(el('span', 'cs-line-no', String(match.line)));
      row.appendChild(highlightPreview(match.text, match.ranges));
      const index = rows.length;
      row.addEventListener('click', () => {
        activeIndex = index;
        openAt(path, match.line);
      });
      group.appendChild(row);
      rows.push({ el: row, path, line: match.line });
      rendered += 1;
    }
    dom.contentSearchResults.appendChild(group);
  }

  /** Build the line preview with the matched spans wrapped for highlighting. */
  function highlightPreview(text, ranges) {
    const span = el('span', 'cs-line-text');
    if (!ranges || ranges.length === 0) {
      span.textContent = text;
      return span;
    }
    let cursor = 0;
    for (const [start, end] of ranges) {
      if (start > cursor) span.appendChild(document.createTextNode(text.slice(cursor, start)));
      span.appendChild(el('span', 'cs-hit', text.slice(start, end)));
      cursor = end;
    }
    if (cursor < text.length) span.appendChild(document.createTextNode(text.slice(cursor)));
    return span;
  }

  function openAt(path, line) {
    ctx.openFile(path, { lines: { start: line, end: line } });
    close();
  }

  function setActive(index) {
    if (rows.length === 0) return;
    if (activeIndex >= 0 && rows[activeIndex]) rows[activeIndex].el.classList.remove('active');
    activeIndex = Math.max(0, Math.min(index, rows.length - 1));
    const entry = rows[activeIndex];
    entry.el.classList.add('active');
    entry.el.scrollIntoView({ block: 'nearest' });
  }

  function onKey(event) {
    if (event.key === 'Escape') {
      event.preventDefault();
      close();
    } else if (event.key === 'ArrowDown') {
      event.preventDefault();
      setActive(activeIndex + 1);
    } else if (event.key === 'ArrowUp') {
      event.preventDefault();
      setActive(activeIndex - 1);
    } else if (event.key === 'Enter') {
      event.preventDefault();
      const entry = rows[activeIndex] || rows[0];
      if (entry) openAt(entry.path, entry.line);
    }
  }

  return { open, close, isOpen, run };
}
