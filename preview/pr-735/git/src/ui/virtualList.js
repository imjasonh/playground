/**
 * Windowed-list helpers. The sidebar tree (and, on big repos, the filter and
 * palette results) can run to many thousands of rows; debouncing the filter
 * only cuts compute per keystroke, but building tens of thousands of DOM nodes
 * is the real cost. These helpers let a list render only the rows near the
 * viewport while a pair of paddings keeps the scrollbar sized for the whole
 * list.
 */

/**
 * Compute the slice of fixed-height rows to render for the current scroll
 * position, plus the top/bottom padding that preserves total scroll height.
 *
 * Falls back to rendering everything when the row height or viewport height is
 * unknown (list not laid out yet, or hidden), so content is never missing —
 * windowing only engages once there is a real viewport to measure against.
 *
 * @param {{scrollTop?: number, viewportHeight?: number, rowHeight?: number, total?: number, overscan?: number}} opts
 * @returns {{start: number, end: number, padTop: number, padBottom: number}}
 */
export function computeWindow({
  scrollTop = 0,
  viewportHeight = 0,
  rowHeight = 0,
  total = 0,
  overscan = 8,
} = {}) {
  if (total <= 0) return { start: 0, end: 0, padTop: 0, padBottom: 0 };
  if (rowHeight <= 0 || viewportHeight <= 0) {
    return { start: 0, end: total, padTop: 0, padBottom: 0 };
  }

  const safeTop = Math.max(0, scrollTop);
  const first = Math.floor(safeTop / rowHeight);
  const visible = Math.ceil(viewportHeight / rowHeight);
  const start = Math.max(0, first - overscan);
  const end = Math.min(total, first + visible + overscan);

  return {
    start,
    end,
    padTop: start * rowHeight,
    padBottom: Math.max(0, (total - end) * rowHeight),
  };
}

/**
 * Measure one row's height by briefly mounting a probe built by `build()`.
 * Returns 0 when the container isn't laid out (callers then render everything).
 *
 * @param {HTMLElement} container  the element rows are appended to
 * @param {() => HTMLElement} build  builds a representative row
 * @returns {number} the row height in pixels, or 0 if unmeasurable
 */
export function measureRowHeight(container, build) {
  const probe = build();
  probe.style.visibility = 'hidden';
  container.appendChild(probe);
  const height = probe.offsetHeight;
  container.removeChild(probe);
  return height || 0;
}
