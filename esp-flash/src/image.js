import {
  ESP_IMAGE_MAGIC,
  OTA_0_OFFSET,
  OTA_1_OFFSET,
  OTA_SLOT_BYTES,
} from "./constants.js";

/**
 * Inspect a firmware blob and decide whether it can go in an inkbot OTA slot.
 *
 * @param {Uint8Array} bytes
 * @returns {{ size: number, magic: number, flashAddress: number }}
 */
export function inspectImage(bytes) {
  if (!(bytes instanceof Uint8Array)) {
    throw new Error("firmware must be a Uint8Array");
  }
  if (bytes.length === 0) {
    throw new Error("firmware is empty");
  }
  if (bytes[0] !== ESP_IMAGE_MAGIC) {
    throw new Error(
      `not an ESP image (first byte is 0x${bytes[0].toString(16).padStart(2, "0")}, want 0x${ESP_IMAGE_MAGIC.toString(16)})`,
    );
  }
  if (bytes.length > OTA_SLOT_BYTES) {
    throw new Error(
      `firmware is ${bytes.length} bytes; OTA slot is ${OTA_SLOT_BYTES} bytes`,
    );
  }
  return {
    size: bytes.length,
    magic: bytes[0],
    flashAddress: OTA_0_OFFSET,
  };
}

/**
 * Build the esptool-js `fileArray` for an app image.
 *
 * Writing both OTA slots means the running slot is replaced no matter which
 * one otadata currently selects. NVS is left alone.
 *
 * @param {Uint8Array} firmware
 * @param {{ bothSlots?: boolean }} [opts]
 * @returns {{ data: Uint8Array, address: number }[]}
 */
export function flashParts(firmware, opts = {}) {
  inspectImage(firmware);
  const bothSlots = opts.bothSlots !== false;
  const parts = [{ data: firmware, address: OTA_0_OFFSET }];
  if (bothSlots) {
    parts.push({ data: firmware, address: OTA_1_OFFSET });
  }
  return parts;
}

/**
 * True when `chipName` from esptool looks like classic ESP32, not S2/S3/C3/C6/H2/P4.
 *
 * @param {string} chipName
 */
export function isClassicEsp32(chipName) {
  const n = String(chipName || "").toUpperCase();
  if (!n.includes("ESP32")) {
    return false;
  }
  return !/ESP32-[SCHP]/.test(n);
}

/**
 * Format a byte count for the status line.
 *
 * @param {number} n
 */
export function formatBytes(n) {
  if (!Number.isFinite(n) || n < 0) {
    return "0 B";
  }
  if (n < 1024) {
    return `${n} B`;
  }
  if (n < 1024 * 1024) {
    return `${(n / 1024).toFixed(1)} KiB`;
  }
  return `${(n / (1024 * 1024)).toFixed(2)} MiB`;
}
