// Small formatting helpers for the UI.

/** Format a byte count as a short human string (e.g. 1.4 KiB). */
export function formatBytes(n) {
  if (n < 1024) return `${n} B`;
  const units = ["KiB", "MiB", "GiB", "TiB"];
  let value = n / 1024;
  let i = 0;
  while (value >= 1024 && i < units.length - 1) {
    value /= 1024;
    i += 1;
  }
  return `${value.toFixed(value >= 10 ? 0 : 1)} ${units[i]}`;
}

/** Abbreviate an oid to its first 8 characters. */
export function shortOid(oid) {
  return oid ? oid.slice(0, 8) : "";
}

/** Format a ratio as a percentage string. */
export function formatPercent(ratio) {
  return `${(ratio * 100).toFixed(1)}%`;
}
