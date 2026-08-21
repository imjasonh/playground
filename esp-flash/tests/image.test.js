import { ESP_IMAGE_MAGIC, OTA_0_OFFSET, OTA_1_OFFSET, OTA_SLOT_BYTES } from "../src/constants.js";
import {
  flashParts,
  formatBytes,
  inspectImage,
  isClassicEsp32,
} from "../src/image.js";
import test from "node:test";
import assert from "node:assert/strict";

function image(size, magic = ESP_IMAGE_MAGIC) {
  const bytes = new Uint8Array(size);
  bytes[0] = magic;
  return bytes;
}

test("inspectImage accepts an ESP app image that fits an OTA slot", () => {
  const info = inspectImage(image(128));
  assert.equal(info.size, 128);
  assert.equal(info.magic, ESP_IMAGE_MAGIC);
  assert.equal(info.flashAddress, OTA_0_OFFSET);
});

test("inspectImage rejects an empty buffer, wrong magic, and oversized blob", () => {
  assert.throws(() => inspectImage(new Uint8Array()), /empty/);
  assert.throws(() => inspectImage(image(16, 0x00)), /not an ESP image/);
  assert.throws(() => inspectImage(image(OTA_SLOT_BYTES + 1)), /OTA slot/);
});

test("flashParts writes ota_0 and ota_1 by default", () => {
  const firmware = image(64);
  const parts = flashParts(firmware);
  assert.equal(parts.length, 2);
  assert.equal(parts[0].address, OTA_0_OFFSET);
  assert.equal(parts[1].address, OTA_1_OFFSET);
  assert.equal(parts[0].data, firmware);
  assert.equal(parts[1].data, firmware);
});

test("flashParts can write only ota_0", () => {
  const parts = flashParts(image(32), { bothSlots: false });
  assert.deepEqual(
    parts.map((p) => p.address),
    [OTA_0_OFFSET],
  );
});

test("isClassicEsp32 accepts ESP32 and rejects later families", () => {
  assert.equal(isClassicEsp32("ESP32"), true);
  assert.equal(isClassicEsp32("ESP32-D0WDQ6 (revision v1.0)"), true);
  assert.equal(isClassicEsp32("ESP32-S3"), false);
  assert.equal(isClassicEsp32("ESP32-C3"), false);
  assert.equal(isClassicEsp32("ESP8266"), false);
  assert.equal(isClassicEsp32(""), false);
});

test("formatBytes uses KiB and MiB", () => {
  assert.equal(formatBytes(200), "200 B");
  assert.equal(formatBytes(2048), "2.0 KiB");
  assert.equal(formatBytes(1024 * 1024), "1.00 MiB");
});
