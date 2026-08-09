# Container Lab runtime assets

This directory is what the Container Lab experiment serves to its `WKWebView`
from the in-app loopback origin. It is the *only* place in the app where guest
code can execute, because WebKit's is the only JIT iOS lets a third-party app
use.

## What is in git

| Path | What it is |
|------|-----------|
| `index.html` | The runtime page: wires xterm-pty to the emulator's TTY and reports boot progress back to Swift over `window.webkit.messageHandlers.containerLab` |
| `vendor/xterm.js`, `vendor/xterm.css` | [xterm.js](https://xtermjs.org) 5.3.0, vendored so the page needs no network |
| `vendor/xterm-pty.js` | [xterm-pty](https://github.com/mame/xterm-pty) 0.10.1, the blocking-TTY shim emscripten programs expect |
| `fetch-runtime.sh` | Installs the built emulator into this directory |

## What is not in git

The emulator itself: `out.js` and `load.js` (emscripten glue), `arg-module.js`
(QEMU's command line), and the wasm plus its packaged guest, which are named
for the emulated machine — `qemu-system-aarch64.wasm` (56 MB) and
`qemu-system-aarch64.data` (187 MB, holding the kernel, EDK2 firmware, and the
baked-in rootfs). A quarter of a gigabyte of generated output, so the repo
tracks the recipe rather than the result, the same way `life-lab` keeps its
wasm build script next to the app.

Build it with the **Container runtime** workflow
(`.github/workflows/container-runtime.yml`), then:

```bash
ios/ContainerRuntime/fetch-runtime.sh --from-run <run-id>      # needs gh
ios/ContainerRuntime/fetch-runtime.sh --from-zip ~/Downloads/container-runtime-aarch64.zip
ios/ContainerRuntime/fetch-runtime.sh --from-dir /tmp/out-js/htdocs
```

Or build locally on a machine with Docker + buildx. c2w v0.8.4 cannot fetch its
own build inputs any more, so prepare them first — see the comments in
`prepare-c2w-build.sh` for what it works around:

```bash
mkdir -p /tmp/out-js/htdocs && cd /tmp/out-js
bash "$REPO"/.github/scripts/prepare-c2w-build.sh v0.8.4
c2w --to-js --target-arch=aarch64 \
  --dockerfile "$PWD/Dockerfile.c2w" --assets "$PWD/c2w-src" \
  arm64v8/alpine:3.20 /tmp/out-js/htdocs/
"$REPO"/ios/ContainerRuntime/fetch-runtime.sh --from-dir /tmp/out-js/htdocs
```

To check the result actually boots before putting it on a phone, serve it and
drive it headlessly the way CI does:

```bash
npm install --no-save --prefix "$REPO"/.github/scripts playwright@1
( cd "$REPO"/.github/scripts && npx playwright install chromium webkit )
node "$REPO"/.github/scripts/container-runtime-boot-smoke.mjs /tmp/out-js/htdocs
node "$REPO"/.github/scripts/container-runtime-boot-smoke.mjs /tmp/out-js/htdocs --browser webkit
```

Both should print `alpine booted and answered as Linux aarch64` in well under a
minute. The WebKit leg matters most: it is the same engine `WKWebView` uses.

`project.yml` picks this directory up as an optional resource folder, so the
app builds either way. When `out.js` is absent, Container Lab says the runtime
is missing instead of pretending it can run something.

## Why the loopback server

The page needs `SharedArrayBuffer` (QEMU Wasm uses wasm threads), which needs
cross-origin isolation, which needs `Cross-Origin-Opener-Policy: same-origin`
and `Cross-Origin-Embedder-Policy: require-corp` response headers. In a
`WKWebView` a custom `WKURLSchemeHandler` scheme is not a secure context and
the service-worker COOP/COEP shims that work in Safari are ignored, so the app
runs a small HTTP server on `127.0.0.1` and sets those headers itself. This is
the same requirement container2wasm documents for its Apache example
(`xterm-pty.conf`).
