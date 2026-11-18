// Turn a git upload-pack side band and a byte count into one status line.
//
// The server overwrites a single line with carriage returns
// ("Counting objects:  40% (12/30)\r"). A fetch also reports how many response
// bytes have arrived. This module keeps the latest of each and decides which
// one the status line should show.

import { formatBytes } from "./format.js";

const DOWNLOAD_AFTER = 64 * 1024;

/** Parse one git progress line, or return null when it isn't one. */
export function parseGitProgressLine(line) {
  let text = line.trim();
  if (text.startsWith("remote:")) text = text.slice("remote:".length).trim();
  if (!text) return null;

  const phase = text.match(
    /^(Enumerating|Counting|Compressing) objects:\s+(?:(\d+)%\s*)?(?:\((\d+)\/(\d+)\)|(\d+))?(?:,\s*done\.)?/,
  );
  if (phase && (phase[2] || phase[3] || phase[5])) {
    const percent = phase[2] != null ? Number(phase[2]) : null;
    const done = phase[3] != null ? Number(phase[3]) : phase[5] != null ? Number(phase[5]) : null;
    const total = phase[4] != null ? Number(phase[4]) : null;
    return {
      stage: phase[1].toLowerCase(),
      label: `${phase[1]} objects`,
      percent,
      done,
      total,
      finished: /done\.\s*$/.test(text),
    };
  }

  const packed = text.match(/^Total\s+(\d+)\s+\(delta\s+(\d+)\)/);
  if (!packed) return null;
  return {
    stage: "total",
    label: "Pack ready",
    percent: null,
    done: Number(packed[1]),
    total: null,
    finished: true,
  };
}

/** Fold a side-band progress stream into the latest parsed line. */
export function createServerProgress() {
  let buf = "";
  let current = null;
  return {
    push(text) {
      buf += String(text).replaceAll("\0", "");
      const parts = buf.split(/\r\n|\r|\n/);
      buf = parts.pop() ?? "";
      for (const part of parts) {
        const parsed = parseGitProgressLine(part);
        if (parsed) current = parsed;
      }
      // A chunk often ends mid-update. Trust the tail only once it has a
      // percentage or a count, so "Compressing objects:  1" doesn't count as
      // 1 object while the rest of "10%" is still on the wire.
      if (/%|\bdone\.|\(\d+\/\d+\)|\d/.test(buf)) {
        const partial = parseGitProgressLine(buf);
        if (partial && (partial.percent != null || partial.finished || partial.total != null)) {
          current = partial;
        }
      }
      return current;
    },
    current() {
      return current;
    },
  };
}

/** Collapse the raw side-band log to one line per update, for the pack card. */
export function tidyServerProgress(text) {
  return text
    .replace(/\r\n|\r/g, "\n")
    .replace(/[ \t]+\n/g, "\n")
    .replace(/\n{2,}/g, "\n")
    .trim();
}

/** Seconds since the activity started, blank under a second. */
export function formatElapsed(ms) {
  if (ms < 1000) return "";
  const total = Math.floor(ms / 1000);
  const minutes = Math.floor(total / 60);
  const seconds = total % 60;
  if (minutes === 0) return `${seconds}s`;
  return `${minutes}:${String(seconds).padStart(2, "0")}`;
}

/** Average throughput, blank until a fraction of a second of bytes. */
export function formatRate(bytes, elapsedMs) {
  if (elapsedMs < 400 || bytes <= 0) return "";
  return `${formatBytes(Math.round(bytes / (elapsedMs / 1000)))}/s`;
}

/**
 * The status line while a pack is in flight.
 *
 * Server phases lead until the body is actually flowing (or the server says
 * the pack is ready). After that the line is bytes received. `scope` is the
 * fetch the user asked for, such as "all 12 branches".
 */
export function describeTransfer({ server = null, bytes = 0, totalBytes = null, elapsedMs = 0, scope = "pack" }) {
  const elapsed = formatElapsed(elapsedMs);
  const serverLeading =
    server &&
    server.stage !== "total" &&
    !server.finished &&
    bytes < DOWNLOAD_AFTER;
  if (serverLeading) {
    const counts =
      server.done != null && server.total != null
        ? `${server.done.toLocaleString()} of ${server.total.toLocaleString()}`
        : "";
    return {
      text: server.percent == null ? server.label : `${server.label}, ${server.percent}%`,
      detail: joinDetail([counts, elapsed]),
      done: server.percent,
      total: server.percent == null ? null : 100,
    };
  }
  if (bytes > 0) {
    const size = totalBytes
      ? `${formatBytes(bytes)} of ${formatBytes(totalBytes)}`
      : formatBytes(bytes);
    return {
      text: `Downloading ${scope}, ${size}`,
      detail: joinDetail([formatRate(bytes, elapsedMs), elapsed]),
      done: totalBytes ? bytes : null,
      total: totalBytes,
    };
  }
  if (server) {
    return {
      text: server.finished ? `${server.label} done` : server.label,
      detail: elapsed,
      done: server.percent,
      total: server.percent == null ? null : 100,
    };
  }
  return { text: `Fetching ${scope}`, detail: elapsed, done: null, total: null };
}

function joinDetail(parts) {
  return parts.filter(Boolean).join(" · ");
}
