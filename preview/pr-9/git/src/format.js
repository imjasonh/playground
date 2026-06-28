/** Presentation helpers (pure, dependency-free). */

/** Human-readable byte size, e.g. 1536 -> "1.5 KB". */
export function formatBytes(bytes) {
  const n = Number(bytes);
  if (!Number.isFinite(n) || n < 0) return '';
  if (n < 1024) return `${n} B`;
  const units = ['KB', 'MB', 'GB', 'TB'];
  let value = n / 1024;
  let unit = 0;
  while (value >= 1024 && unit < units.length - 1) {
    value /= 1024;
    unit += 1;
  }
  const rounded = value >= 100 ? Math.round(value) : Math.round(value * 10) / 10;
  return `${rounded} ${units[unit]}`;
}

/** Abbreviated commit id. */
export function shortOid(oid, length = 7) {
  if (!oid) return '';
  return String(oid).slice(0, length);
}

/** First line of a commit message. */
export function commitSummary(message) {
  if (!message) return '';
  const line = String(message).split('\n', 1)[0].trim();
  return line;
}

const MINUTE = 60;
const HOUR = 60 * MINUTE;
const DAY = 24 * HOUR;
const MONTH = 30 * DAY;
const YEAR = 365 * DAY;

/**
 * Relative time label from a UNIX timestamp (seconds).
 *
 * @param {number} timestampSeconds
 * @param {number} [nowMs] current time in ms (injectable for tests)
 */
export function relativeTime(timestampSeconds, nowMs = Date.now()) {
  if (!Number.isFinite(timestampSeconds)) return '';
  const deltaSeconds = Math.round(nowMs / 1000 - timestampSeconds);
  if (deltaSeconds < 0) return 'in the future';
  if (deltaSeconds < 45) return 'just now';

  const pick = (value, unit) => {
    const rounded = Math.round(value);
    return `${rounded} ${unit}${rounded === 1 ? '' : 's'} ago`;
  };

  if (deltaSeconds < HOUR) return pick(deltaSeconds / MINUTE, 'minute');
  if (deltaSeconds < DAY) return pick(deltaSeconds / HOUR, 'hour');
  if (deltaSeconds < MONTH) return pick(deltaSeconds / DAY, 'day');
  if (deltaSeconds < YEAR) return pick(deltaSeconds / MONTH, 'month');
  return pick(deltaSeconds / YEAR, 'year');
}
