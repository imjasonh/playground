/**
 * Shared rendering for fuzzy-match rows (the sidebar filter results and the
 * command palette render the same two-line "name + path" shape, only the CSS
 * class names differ).
 */
import { el } from './dom.js';
import { highlightSegments } from '../fuzzy.js';
import { basename } from '../pathUtils.js';

function highlightedSpan(className, text, positions) {
  const span = el('span', className);
  for (const segment of highlightSegments(text, positions)) {
    span.appendChild(el('span', segment.match ? 'match' : null, segment.text));
  }
  return span;
}

/**
 * Append the highlighted file name and full path to a result row.
 *
 * @param {HTMLElement} row
 * @param {{item: string, target: string, positions: number[]}} result
 * @param {string} nameClass  CSS class for the file-name span
 * @param {string} pathClass  CSS class for the full-path span
 */
export function appendMatch(row, result, nameClass, pathClass) {
  // The fuzzy match positions are over the full path; translate the ones that
  // land in the basename so the file name highlights line up too.
  const nameStart = result.target.length - basename(result.target).length;
  const namePositions = result.positions
    .filter((p) => p >= nameStart)
    .map((p) => p - nameStart);
  row.appendChild(highlightedSpan(nameClass, basename(result.item), namePositions));
  row.appendChild(highlightedSpan(pathClass, result.item, result.positions));
}
