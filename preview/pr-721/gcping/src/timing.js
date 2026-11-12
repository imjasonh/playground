// Resource Timing exposes DNS/TCP/TLS/wait only when the response
// includes Timing-Allow-Origin. Cross-origin entries without that
// header keep duration but zero the rest of the timestamps.
export function breakdownFromEntry(entry) {
  if (!entry) {
    return null;
  }
  if (!(entry.connectStart > 0 || entry.requestStart > 0)) {
    return null;
  }
  const dns = ms(entry.domainLookupEnd - entry.domainLookupStart);
  let tcp = 0;
  let tls = 0;
  if (entry.secureConnectionStart > 0) {
    tcp = ms(entry.secureConnectionStart - entry.connectStart);
    tls = ms(entry.connectEnd - entry.secureConnectionStart);
  } else if (entry.connectEnd > 0) {
    tcp = ms(entry.connectEnd - entry.connectStart);
  }
  const wait = ms(entry.responseStart - entry.requestStart);
  const download = ms(entry.responseEnd - entry.responseStart);
  return { dns, tcp, tls, wait, download };
}

function ms(value) {
  if (value < 0) {
    return 0;
  }
  return value;
}
