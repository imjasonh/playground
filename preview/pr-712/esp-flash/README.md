# ESP32 flash

A static page that writes an ESP32 app image over USB. Chrome and Edge on a
computer use the Web Serial API. Chrome on Android uses WebUSB and
[web-serial-polyfill](https://github.com/google/web-serial-polyfill).
[esptool-js](https://github.com/espressif/esptool-js) speaks the ESP ROM
bootloader.

Safari and Firefox do not expose either API, so this page cannot flash from
those browsers.

## What it writes

The GHCR packages
[`inkbot-esp32`](https://github.com/imjasonh/playground/pkgs/container/playground%2Finkbot-esp32)
and
[`maze-esp32`](https://github.com/imjasonh/playground/pkgs/container/playground%2Fmaze-esp32)
are the same `firmware.bin` files the desk frame pulls for OTA. You can also
choose a local `.bin`, for example the output of `make save-image` in
[`inkbot-esp32`](../inkbot-esp32/).

The write goes to both OTA app slots (`0x20000` and `0x210000`). NVS is not
erased, so Wi-Fi and trust keys survive. This is the browser equivalent of
`make flash`, not `make bootstrap`.

A board that still has the factory partition table cannot boot these slots.
Flash that layout once with `make bootstrap` on a machine that has the
ESP-IDF tree, then use this page for later app images.

This page does not verify Cosign. Device OTA still does. Flash from a computer
you trust.

## Run locally

Serve the page over `http://localhost`. Web Serial needs a secure context, and
`file://` is not one.

```bash
cd esp-flash
npm install
npm run vendor   # copies esptool-js and the WebUSB polyfill into vendor/
npm start
```

Then open http://localhost:3000, load an image, plug in the board, and click
**Connect and flash**. If the ROM bootloader does not appear, hold **BOOT**,
tap **RESET**, and try again.

E-ink keeps the last picture until the new firmware paints. A 7.5-inch full
refresh takes several seconds. The page pulses EN after the write so the app
can boot. If the picture still has not changed after that, tap **RESET**
without holding **BOOT**. The CH9102 auto-reset circuit can leave the chip in
the ROM bootloader after the serial port closes.

GHCR fetches go through the deployed
[`cors-proxy`](../cors-proxy/) Worker because `ghcr.io` does not send CORS
headers. If you run your own Worker, add `?proxy=`.

## Tests

```bash
npm test
```

The tests cover image checks, GHCR URL construction, a mocked registry pull,
and serial-API selection. They do not open a real serial port.
