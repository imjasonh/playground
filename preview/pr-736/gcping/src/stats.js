// Median of a numeric sample. For an even count, uses the higher of the
// two central values, matching GCPing's floor(n/2) pick after sort.
export function median(values) {
  if (values.length === 0) {
    return null;
  }
  const copy = values.slice();
  copy.sort((a, b) => a - b);
  return copy[Math.floor(copy.length / 2)];
}

export function compareResults(a, b, sortKey, sortDir) {
  let mul = -1;
  if (sortDir === "ascending") {
    mul = 1;
  }
  if (sortKey === "median") {
    const aMissing = a.median === null;
    const bMissing = b.median === null;
    if (aMissing && bMissing) {
      return a.location.localeCompare(b.location, "en");
    }
    if (aMissing) {
      return 1;
    }
    if (bMissing) {
      return -1;
    }
    if (a.median !== b.median) {
      if (a.median > b.median) {
        return mul;
      }
      return -mul;
    }
    return a.location.localeCompare(b.location, "en");
  }
  const av = a[sortKey];
  const bv = b[sortKey];
  if (av === bv) {
    return a.id.localeCompare(b.id, "en");
  }
  return mul * String(av).localeCompare(String(bv), "en");
}

export function fastestId(rows) {
  let bestId = null;
  let bestMedian = null;
  for (const row of rows) {
    if (row.median !== null && (bestMedian === null || row.median < bestMedian)) {
      bestMedian = row.median;
      bestId = row.id;
    }
  }
  return bestId;
}
