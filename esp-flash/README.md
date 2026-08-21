# ESP32 flash

A static page that writes an ESP32 app image over USB. Desktop Chrome and Edge
use the Web Serial API. Android Chrome uses WebUSB through
[web-serial-polyfill](https://github.com/google/web-serial-polyfill). The
protocol is still the ESP ROM bootloader; [esptool-js](https://github.com/espressif/esptool-js)
speaks it.

Safari and Firefox do not expose either API, so this page cannot flash from
those browsers.

## What it writes

The GHCR packages
[`inkbot-esp32`](https://github.com/imjasonh/playground/pkgs/container/playground%2Finkbot-esp32)
and
[`maze-esp32`](https://github.com/imjasonh/playground/pkgs/container/playground%2Fmaze-esp32)
are the same `firmware.bin` files the desk frame pulls for OTA. You can also
choose a local `.bin` (for example the output of `make save-image` in
[`inkbot-esp32`](../inkbot-esp32/)).

The write goes to the OTA app slots at `0x20000` and, by default, `0x210000`.
NVS is not erased, so Wi-Fi and trust keys survive. This is the browser
equivalent of `make flash`, not `make bootstrap`.

A board that still has the factory partition table cannot boot these slots.
Flash that layout once with `make bootstrap` on a machine that has the
ESP-IDF tree, then use this page for later app images.

This page does not verify Cosign. Device OTA still does. Treat a USB flash as
something you do from a computer you trust.

## Run locally

Serve over `http://localhost` (not `file://`). Web Serial is a secure-context
API, and `localhost` counts.

```bash
cd esp-flash
npm install
npm run vendor   # copies esptool-js and the WebUSB polyfill into vendor/
npm start
```

Then open http://localhost:3000, load an image, plug in the board, and click
**Connect and flash**. If the ROM bootloader does not appear, hold **BOOT**,
tap **RESET**, and try again.

GHCR fetches go through the deployed
[`cors-proxy`](../cors-proxy/) Worker because `ghcr.io` does not send CORS
headers. Override the proxy with `?proxy=` if you run your own.

## Tests

```bash
npm test
```

The tests cover image checks, GHCR URL construction, a mocked registry pull,
and serial-API selection. They do not open a real serial port.
