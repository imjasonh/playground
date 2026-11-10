import { getSerial, requestPort } from "../src/serial.js";
import test from "node:test";
import assert from "node:assert/strict";

test("getSerial prefers Web Serial when navigator.serial exists", async () => {
  const serial = { requestPort: async () => ({ id: "native" }) };
  const got = await getSerial({
    navigator: { serial, usb: { requestDevice: async () => ({}) } },
  });
  assert.equal(got.kind, "web-serial");
  assert.equal(got.serial, serial);
});

test("getSerial falls back to the WebUSB serial polyfill", async () => {
  const polyfill = { requestPort: async () => ({ id: "usb" }) };
  const got = await getSerial({
    navigator: { usb: { requestDevice: async () => ({}) } },
    loadPolyfill: async () => ({ serial: polyfill }),
  });
  assert.equal(got.kind, "webusb-polyfill");
  assert.equal(got.serial, polyfill);
});

test("getSerial reports none when neither API exists", async () => {
  const got = await getSerial({ navigator: {} });
  assert.equal(got.kind, "none");
  assert.equal(got.serial, null);
});

test("requestPort rejects when no serial implementation is present", async () => {
  await assert.rejects(() => requestPort(null), /unavailable/);
});
