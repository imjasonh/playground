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

The emulator itself: `out.js`, `out.wasm`, `load.js`, `arg-module.js` (plus any
emscripten side files). That is tens of megabytes of generated wasm, so the
repo tracks the recipe rather than the output, the same way `life-lab` keeps
its wasm build script next to the app.

Build it with the **Container runtime** workflow
(`.github/workflows/container-runtime.yml`), then:

```bash
ios/ContainerRuntime/fetch-runtime.sh --from-run <run-id>      # needs gh
ios/ContainerRuntime/fetch-runtime.sh --from-zip ~/Downloads/container-runtime-aarch64.zip
ios/ContainerRuntime/fetch-runtime.sh --from-dir /tmp/out-js/htdocs
```

Or build locally on a machine with Docker + buildx:

```bash
mkdir -p /tmp/out-js/htdocs
c2w --to-js --target-arch=aarch64 arm64v8/alpine:3.20 /tmp/out-js/htdocs/
ios/ContainerRuntime/fetch-runtime.sh --from-dir /tmp/out-js/htdocs
```

`project.yml` picks this directory up as an optional resource folder, so the
app builds either way. When `out.wasm` is absent, Container Lab says the
runtime is missing instead of pretending it can run something.

## Why the loopback server

The page needs `SharedArrayBuffer` (QEMU Wasm uses wasm threads), which needs
cross-origin isolation, which needs `Cross-Origin-Opener-Policy: same-origin`
and `Cross-Origin-Embedder-Policy: require-corp` response headers. In a
`WKWebView` a custom `WKURLSchemeHandler` scheme is not a secure context and
the service-worker COOP/COEP shims that work in Safari are ignored, so the app
runs a small HTTP server on `127.0.0.1` and sets those headers itself. This is
the same requirement container2wasm documents for its Apache example
(`xterm-pty.conf`).
