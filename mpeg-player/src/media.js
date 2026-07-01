export const TS_PACKET_BYTES = 188;
export const TS_PROBE_PACKETS = 6;

export function clamp(value, minimum, maximum) {
  return Math.min(maximum, Math.max(minimum, value));
}

export function formatTime(seconds) {
  if (!Number.isFinite(seconds) || seconds < 0) {
    return "0:00";
  }

  const wholeSeconds = Math.floor(seconds);
  const hours = Math.floor(wholeSeconds / 3600);
  const minutes = Math.floor((wholeSeconds % 3600) / 60);
  const remainder = wholeSeconds % 60;

  if (hours > 0) {
    return `${hours}:${String(minutes).padStart(2, "0")}:${String(remainder).padStart(2, "0")}`;
  }
  return `${minutes}:${String(remainder).padStart(2, "0")}`;
}

export function formatBytes(bytes) {
  if (!Number.isFinite(bytes) || bytes <= 0) {
    return "0 B";
  }

  const units = ["B", "KiB", "MiB", "GiB"];
  const unit = Math.min(
    units.length - 1,
    Math.floor(Math.log(bytes) / Math.log(1024)),
  );
  const value = bytes / 1024 ** unit;
  const precision = unit === 0 || value >= 10 ? 0 : 1;
  return `${value.toFixed(precision)} ${units[unit]}`;
}

/**
 * Returns the byte offset of a 188-byte MPEG transport stream packet sequence.
 * A short prefix before the first packet is tolerated, matching JSMpeg's
 * resynchronization behavior.
 */
export function findTransportStreamOffset(input, minimumPackets = 3) {
  const bytes =
    input instanceof Uint8Array
      ? input
      : new Uint8Array(input.buffer ?? input, input.byteOffset ?? 0, input.byteLength);

  if (bytes.byteLength < TS_PACKET_BYTES * minimumPackets) {
    return -1;
  }

  const lastOffset = Math.min(TS_PACKET_BYTES - 1, bytes.byteLength - 1);
  for (let offset = 0; offset <= lastOffset; offset += 1) {
    let matches = 0;
    for (
      let position = offset;
      position < bytes.byteLength;
      position += TS_PACKET_BYTES
    ) {
      if (bytes[position] !== 0x47) {
        break;
      }
      matches += 1;
      if (matches >= minimumPackets) {
        return offset;
      }
    }
  }

  return -1;
}

export function normalizeMediaUrl(value, baseUrl = globalThis.location?.href) {
  const input = String(value ?? "").trim();
  if (!input) {
    throw new Error("Enter an MPEG-TS URL.");
  }

  let url;
  try {
    url = new URL(input, baseUrl);
  } catch {
    throw new Error("Enter a valid URL.");
  }

  if (!["http:", "https:"].includes(url.protocol)) {
    throw new Error("Only HTTP and HTTPS URLs are supported.");
  }
  return url.href;
}
