// File-transfer protocol helpers for the WebRTC app.
//
// Files are sent over the WebRTC data channel as a short JSON "meta" control
// message, followed by a sequence of binary chunks, then a JSON "end" message.
// The data channel is ordered and reliable, so chunks arrive in order and can
// be reassembled without per-chunk headers.
//
// The functions here are pure and DOM-free (aside from the standard `Blob`,
// which exists in both browsers and Node >= 18), so they can be unit tested.

// 16 KiB keeps each send comfortably under the data-channel message-size limit
// that browsers negotiate, while staying large enough for good throughput.
export const CHUNK_SIZE = 16 * 1024;

// Control-message kinds sent as JSON strings over the channel.
export const MESSAGE_KIND = {
  chat: "chat",
  fileMeta: "file-meta",
  fileEnd: "file-end",
};

let metaCounter = 0;

// Build the JSON meta message announcing an incoming file.
export function createFileMeta(file, chunkSize = CHUNK_SIZE) {
  if (!file || typeof file.size !== "number") {
    throw new TypeError("createFileMeta expects a file-like object with a size");
  }
  const size = file.size;
  metaCounter += 1;
  return {
    kind: MESSAGE_KIND.fileMeta,
    id: `${Date.now().toString(36)}-${metaCounter}`,
    name: typeof file.name === "string" && file.name ? file.name : "download",
    size,
    mime: typeof file.type === "string" ? file.type : "",
    chunks: countChunks(size, chunkSize),
  };
}

// A chat text message envelope.
export function createChatMessage(text) {
  return { kind: MESSAGE_KIND.chat, text: String(text) };
}

// The trailer message marking a file complete.
export function createFileEnd(id) {
  return { kind: MESSAGE_KIND.fileEnd, id };
}

// How many chunks a file of `size` bytes splits into.
export function countChunks(size, chunkSize = CHUNK_SIZE) {
  if (!Number.isFinite(size) || size < 0) {
    throw new RangeError("size must be a non-negative number");
  }
  if (!Number.isFinite(chunkSize) || chunkSize <= 0) {
    throw new RangeError("chunkSize must be a positive number");
  }
  return Math.ceil(size / chunkSize);
}

// Compute the [start, end) byte ranges for slicing a file into chunks.
export function chunkRanges(size, chunkSize = CHUNK_SIZE) {
  const ranges = [];
  for (let start = 0; start < size; start += chunkSize) {
    ranges.push({ start, end: Math.min(start + chunkSize, size) });
  }
  return ranges;
}

// Human-friendly byte formatting for progress UI.
export function formatBytes(bytes) {
  if (!Number.isFinite(bytes) || bytes < 0) return "0 B";
  const units = ["B", "KB", "MB", "GB", "TB"];
  let value = bytes;
  let unit = 0;
  while (value >= 1024 && unit < units.length - 1) {
    value /= 1024;
    unit += 1;
  }
  const rounded = unit === 0 ? value : Math.round(value * 10) / 10;
  return `${rounded} ${units[unit]}`;
}

// Reassembles binary chunks for a single incoming file and reports progress.
export class FileAssembler {
  constructor(meta) {
    if (!meta || typeof meta.size !== "number") {
      throw new TypeError("FileAssembler expects a file-meta object");
    }
    this.meta = meta;
    this.parts = [];
    this.received = 0;
  }

  // Add one binary chunk (ArrayBuffer, TypedArray, or Blob). Returns the
  // fraction complete in the range [0, 1].
  addChunk(chunk) {
    const length = chunkByteLength(chunk);
    this.parts.push(chunk);
    this.received += length;
    if (this.meta.size === 0) return 1;
    return Math.min(this.received / this.meta.size, 1);
  }

  get complete() {
    return this.received >= this.meta.size;
  }

  // Assemble the received chunks into a Blob with the announced MIME type.
  toBlob() {
    return new Blob(this.parts, {
      type: this.meta.mime || "application/octet-stream",
    });
  }
}

function chunkByteLength(chunk) {
  if (chunk == null) return 0;
  if (typeof chunk.byteLength === "number") return chunk.byteLength;
  if (typeof chunk.size === "number") return chunk.size;
  return 0;
}
