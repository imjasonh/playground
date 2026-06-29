/**
 * Pure presentation helpers for times and counts. Everything that touches "now"
 * takes it as an argument so the functions are deterministic under test.
 *
 * Clock times render in America/New_York regardless of the viewer's timezone —
 * a countdown to a Manhattan-bound train should read in subway-local time.
 */

const NYC_TZ = 'America/New_York';

/** Fractional minutes from now until a POSIX-seconds time (negative = past). */
export function minutesUntil(timeSeconds, nowMs = Date.now()) {
  if (!Number.isFinite(timeSeconds)) return NaN;
  return (timeSeconds * 1000 - nowMs) / 60000;
}

/** Countdown label: "Now" within ~30s, otherwise whole "N min". */
export function formatCountdown(timeSeconds, nowMs = Date.now()) {
  const minutes = minutesUntil(timeSeconds, nowMs);
  if (!Number.isFinite(minutes)) return '';
  if (minutes < 0.5) return 'Now';
  return `${Math.round(minutes)} min`;
}

/** Wall-clock time in NYC, e.g. "9:07 PM". */
export function clockTime(timeSeconds, { timeZone = NYC_TZ } = {}) {
  if (!Number.isFinite(timeSeconds)) return '';
  const formatter = new Intl.DateTimeFormat('en-US', {
    hour: 'numeric',
    minute: '2-digit',
    timeZone,
  });
  return formatter.format(new Date(timeSeconds * 1000));
}

/** Whole seconds since a POSIX-seconds timestamp. */
export function secondsAgo(timestampSeconds, nowMs = Date.now()) {
  return Math.round(nowMs / 1000 - timestampSeconds);
}

/** Feed-freshness label, e.g. "just now", "42s ago", "3 min ago". */
export function freshness(timestampSeconds, nowMs = Date.now()) {
  if (!Number.isFinite(timestampSeconds)) return 'unknown';
  const seconds = secondsAgo(timestampSeconds, nowMs);
  if (seconds < 10) return 'just now';
  if (seconds < 60) return `${seconds}s ago`;
  const minutes = Math.round(seconds / 60);
  if (minutes < 60) return `${minutes} min ago`;
  const hours = Math.round(minutes / 60);
  return `${hours} hr ago`;
}

/** Tiny pluralizer: `pluralize(2, 'train')` -> "trains". */
export function pluralize(count, singular, plural) {
  return count === 1 ? singular : plural || `${singular}s`;
}
