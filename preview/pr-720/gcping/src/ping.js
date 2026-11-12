import { pingUrl } from "./regions.js";
import { breakdownFromEntry } from "./timing.js";

export const PING_TIMEOUT_MS = 20000;

export async function pingRegion(regionId, options) {
  const nonce = options.nonce;
  const url = pingUrl(regionId, nonce);
  const fetchImpl = options.fetchImpl;
  const now = options.now;
  const getEntry = options.getEntry;
  const signal = combineSignals(options.signal, options.timeoutMs);
  const start = now();
  try {
    await fetchImpl(url, {
      cache: "no-store",
      mode: "no-cors",
      credentials: "omit",
      signal,
    });
  } catch (err) {
    let aborted = false;
    if (err && err.name === "AbortError") {
      aborted = true;
    }
    return { ok: false, aborted, url, duration: null, breakdown: null };
  }
  const duration = now() - start;
  const entry = getEntry(url);
  return {
    ok: true,
    aborted: false,
    url,
    duration,
    breakdown: breakdownFromEntry(entry),
  };
}

function combineSignals(external, timeoutMs) {
  let limit = PING_TIMEOUT_MS;
  if (typeof timeoutMs === "number") {
    limit = timeoutMs;
  }
  const timeout = AbortSignal.timeout(limit);
  if (!external) {
    return timeout;
  }
  if (typeof AbortSignal.any === "function") {
    return AbortSignal.any([external, timeout]);
  }
  return timeout;
}
