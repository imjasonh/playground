/**
 * Resolve a SerialPort factory.
 *
 * Desktop Chrome and Edge expose `navigator.serial` (Web Serial). Android
 * Chrome exposes `navigator.usb` (WebUSB). `web-serial-polyfill` turns that
 * into the SerialPort shape esptool-js already speaks.
 *
 * @param {{
 *   navigator?: { serial?: Serial, usb?: USB },
 *   loadPolyfill?: () => Promise<{ serial: Serial }>,
 * }} [opts]
 * @returns {Promise<{ kind: "web-serial" | "webusb-polyfill" | "none", serial: Serial | null }>}
 */
export async function getSerial(opts = {}) {
  const nav = opts.navigator || (typeof navigator === "undefined" ? {} : navigator);
  if (nav.serial && typeof nav.serial.requestPort === "function") {
    return { kind: "web-serial", serial: nav.serial };
  }
  if (nav.usb && typeof nav.usb.requestDevice === "function") {
    const loadPolyfill = opts.loadPolyfill || defaultLoadPolyfill;
    const mod = await loadPolyfill();
    const serial = mod?.serial;
    if (serial && typeof serial.requestPort === "function") {
      return { kind: "webusb-polyfill", serial };
    }
  }
  return { kind: "none", serial: null };
}

async function defaultLoadPolyfill() {
  return import("../vendor/web-serial-polyfill.js");
}

/**
 * Ask the user to pick a serial (or WebUSB-emulated serial) port.
 *
 * @param {Serial} serial
 * @param {SerialPortRequestOptions} [options]
 */
export async function requestPort(serial, options) {
  if (!serial || typeof serial.requestPort !== "function") {
    throw new Error("Web Serial and WebUSB are both unavailable in this browser");
  }
  return serial.requestPort(options);
}
