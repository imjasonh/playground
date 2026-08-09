# Wasm Service: a wasm HTTP server, delivered by OCI, running on a phone

This is Option C from [`ios-containers-design.md`](ios-containers-design.md)
built out: for a payload that is *already* WebAssembly, no CPU emulation is
needed at all, and the whole thing collapses into an interpreter, a socket, and
a registry client.

The demo it exists to support: **a hello-world Go `net/http` service, compiled
to `wasip1`, published to a registry as an OCI artifact, pulled by an iPhone,
and served over a real TCP port that a laptop can `curl`.**

The payload is [`wasm-hello/`](../wasm-hello/) — ordinary `net/http`, with the
host ABI documented in [its README](../wasm-hello/README.md). The iOS side is
`ios/Sources/Experiments/WasmService/`.

## 1. Why this is not the Container Lab shape

Container Lab runs an emulated arm64 machine inside a `WKWebView`, because
WebKit's wasm JIT is the only dynamic code generation an App Store app can
reach. That buys arbitrary `linux/arm64` images and costs everything else: the
guest lives in a web view, so it cannot be handed a socket, and WebKit
suspends it when the app leaves the foreground.

Wasm Service inverts every one of those trades:

| | Container Lab | Wasm Service |
|---|---|---|
| Payload | any `linux/arm64` image | a wasm module |
| Engine | QEMU Wasm in `WKWebView` (JIT) | WasmKit, interpreted, in-process |
| Speed | slow, but JIT-compiled | interpreted; fine for a request handler |
| Sockets | none — the guest is in a web view | the app owns a real `NWListener` |
| Backgrounding | webview is suspended | ordinary app code (see §5) |
| Memory | WebContent's ~128–256 MB budget | the app's own budget |

Neither replaces the other. The interesting result is that once you accept a
wasm payload, *everything else about the iOS platform stops fighting you*.

## 2. Shape

```
┌─ Playground app ──────────────────────────────────────────────────┐
│                                                                   │
│  RegistryClient ──► OCI artifact ──► WasmArtifact.moduleLayer     │
│   (shared with Container Lab)         picks the application/wasm  │
│                                       blob; digest-verified       │
│                     │                                             │
│                     ▼                                             │
│  WasmModuleStore    cached under its digest in Application        │
│                     Support, so a background window can resume    │
│                     without a network                             │
│                     │                                             │
│  ┌──────────────────▼─────────── guest queue (serial) ─────────┐  │
│  │  WasmHTTPGuest    parse → instantiate → _initialize         │  │
│  │    WASIHost       clock, randomness, argv/env, a log        │  │
│  │    MemoryCap      refuses growth past a ceiling             │  │
│  └──────────────────▲─────────────────────────────────────────┘  │
│                     │ raw HTTP/1.1 bytes, one exchange at a time  │
│  WasmHTTPServer ────┘  NWListener, HTTPRequestFramer              │
│                                                                   │
└───────────────────────────────────────────────────────────────────┘
```

The listener and the guest are on separate queues on purpose. Interpreted wasm
is slow enough that a request in the guest would otherwise stall `accept()`;
and the guest queue is serial because a wasm instance has one linear memory and
one outstanding buffer, so it cannot be entered twice at once.

## 3. Why an interpreter, and why WasmKit

iOS grants no JIT entitlement outside `WKWebView`, so any wasm running as app
code has to be interpreted. That is a real cost and it is also the entire
enabling constraint: an interpreter is ordinary Swift in the reviewed binary,
which means the module is ordinary app code — it can be handed a socket, and it
keeps running in the windows where a web view would have been suspended.

[WasmKit](https://github.com/swiftwasm/WasmKit) is pure Swift, has no binary
dependency, and does not JIT. **Pinned to 0.2.2**: 0.3 raises its floor to iOS
18 and this app deploys to 16.2.

Two things had to be built around it:

- **Its WASI is the wrong shape twice over.** `WasmKitWASI`'s `poll_oneoff`
  returns `ENOTSUP`, and Go's scheduler turns any `poll_oneoff` failure into a
  fatal throw the first time it sleeps — so a Go guest dies on that alone. It
  also wires the guest to the real filesystem, which is the wrong default for
  running a stranger's compiled code on a phone. `WASIHost` implements the
  slice Go actually imports: a clock, randomness, argv/env, stdout/stderr as a
  log, a `poll_oneoff` that sleeps (bounded, because it is on the thread
  serving a request), and `ENOTCAPABLE`/`EBADF` for everything filesystem. No
  preopens means Go concludes it has no filesystem — the same answer `wasmtime`
  gives when started without `--dir`.
- **Every guest pointer is untrusted.** WasmKit's
  `withUnsafeMutableBufferPointer(offset:count:)` does no bounds checking of
  its own, so `GuestMemoryView` checks first and turns an out-of-range offset
  into `EFAULT` for the guest rather than a stray read in the app's address
  space.

`Store.resourceLimiter` — the only way to cap linear-memory growth — is still
`@_spi(Fuzzing)` in 0.2.2, so `WasmHTTPGuest` imports that SPI. The pin makes
that a known quantity, and the alternative is no cap: iOS answers an app that
takes too much by killing it outright, with no error and nothing in the log.

## 4. OCI is only the transport

There is no root filesystem and nothing to `exec`. The manifest carries one
blob that happens to be a wasm module, so `WasmArtifact` skips Container Lab's
layer stacking and just picks a descriptor:

1. a layer whose media type is a known wasm type, or ends in `+wasm`;
2. failing that, the single layer of a manifest whose `artifactType` (or config
   media type) says wasm — which is what `oras push` produces, since it labels
   the layer opaque by default;
3. failing that, a layer whose `org.opencontainers.image.title` ends in
   `.wasm`.

Nobody has standardized these media types, so recognizing the ones in
circulation beats refusing a perfectly good module over a spelling difference.
Pointing the experiment at `alpine:3.20` gets an explanation rather than a
failure halfway through instantiating a tarball.

Because the module travels as a normal OCI blob, **anything that compiles to
`wasip1` works** — Go, Rust, TinyGo, Zig, and JS via a wasm-embedded engine —
as long as it exports the three ABI functions.

## 5. Running in the background, honestly

**There is no way for an App Store app to run a server permanently in the
background.** Nothing in this experiment works around that, because nothing
can. What iOS offers is three windows, and `WasmServiceBackground` uses all
three:

| Window | Length | How |
|---|---|---|
| Foreground | unlimited | with the idle timer disabled and the phone on a charger, this is the "leave it running" mode, and the only genuinely continuous one |
| Background assertion | ~30 s | `beginBackgroundTask`, so a request in flight when the user swipes away still gets an answer |
| `BGProcessingTask` | minutes, system-scheduled | `requiresExternalPower = true`, and each window schedules the next, so a plugged-in phone comes back periodically |

"Only while plugged into power" is a real setting rather than a euphemism:
`requiresExternalPower` makes iOS hold the window back until the phone is
charging. A background window can begin with the app freshly relaunched, which
is why the module is cached under its digest — resuming means reading a file,
not pulling a registry — and why the `BGTaskScheduler` handler is registered in
`PlaygroundApp.init()`, before any view exists.

The paths that *would* run indefinitely are all closed:

- `NEPacketTunnelProvider` / `NEAppPushProvider` need a Network Extension
  entitlement Apple grants case by case, and would run the code in the
  extension rather than the app.
- The `audio` and `location` background modes do keep an app alive, and this
  app already declares both for Snore Log and Ride Monitor. Playing silent
  audio to keep a web server up is a straightforward way to get the whole app
  rejected, so it is not done.

## 6. Reaching it from off the phone

The listener binds every interface by default, so this is mostly a question of
which address you can route to. The experiment enumerates the device's
interfaces and ranks them by usefulness.

**Same Wi-Fi.** The `en0` address works from a laptop immediately. This is the
demo path and needs nothing.

**Anywhere, privately — Tailscale.** This is the recommended answer, and the
happy surprise is that it needs *no code in this app at all*. Tailscale's iOS
client is a `NEPacketTunnelProvider`: when it is connected the device holds a
`100.64.0.0/10` address on a `utun` interface, and inbound tailnet connections
arrive through the ordinary network stack. A socket bound to `0.0.0.0:8080` is
therefore already listening on the tailnet address. `LocalAddresses` detects
the CGNAT range specifically — distinguishing a tailnet from any other VPN,
both of which appear as `utun` — and lists it first, labelled "reachable
anywhere".

Embedding Tailscale *into* the app was considered and rejected. `tsnet` would
put the node inside the app's process, but it is Go, it wants a userspace
WireGuard stack, and it would make the app a VPN client for App Review
purposes; the real client already does the job better, and running both is
strictly worse.

**Public internet.** Deliberately not done here. Tailscale Funnel is configured
per node and the iOS client exposes no controls for it, so the workable shape
is a second tailnet node — a VPS, a Raspberry Pi, a Cloudflare tunnel —
reverse-proxying to the phone's tailnet address. That belongs on the node with
a real CLI, not on the phone, and it keeps the phone from being an origin
server on the open internet, which it should not be while its uptime is
measured in `BGProcessingTask` windows.

## 7. What is tested, and where

| Layer | Test | Runs |
|---|---|---|
| Go handler and HTTP framing | `wasm-hello/wire/wire_test.go` | `go test`, everywhere |
| The wasip1 module, through the real ABI | `wasm-hello/wasm_roundtrip_test.go` | builds the module and drives it under [wazero](https://wazero.io) |
| Host ABI + the WASI host | `ios/Tests/PlaygroundTests/WasmServiceGuestTests.swift` | simulator; modules assembled from WAT at test time, so no binary fixture in git |
| Framing, artifact selection, cache, addresses | `ios/Tests/PlaygroundTests/WasmServiceHostTests.swift` | simulator; no wasm needed |
| The whole demo | `ios/Tests/PlaygroundTests/WasmServiceGoModuleTests.swift` | simulator; `ios.yml` builds `wasm-hello` into `ios/Tests/Fixtures/hello.wasm` first, and the tests skip when it is absent |

The WAT trick that makes the WASI host testable through the same door as
everything else: a test module reports the result of the WASI call it made *as
its HTTP response*, by leaving the bytes in memory and returning that region.
So `guest.handle(…)` hands the test whatever the module saw.

## 8. Limits worth knowing

- **One request at a time.** A wasm instance has one linear memory; concurrency
  would mean one instance per request, and instantiating a Go module takes
  seconds under an interpreter.
- **No keep-alive.** The guest serves serially anyway, so a held-open
  connection would only pin a slot.
- **No chunked request bodies.** De-chunking would have to happen before the
  guest sees the bytes; the framer answers `501` rather than handing over a
  body the guest cannot parse.
- **wasip1 has no sockets**, so the guest cannot make outbound connections
  either. That is a limitation and a feature: the module gets a clock,
  randomness, and a log, and nothing else.
- **Startup is slow.** Parsing, validating, and translating a ~5 MB Go module,
  then starting the Go runtime under an interpreter, takes seconds on a phone.
  It happens once per service, not once per request — that is what the reactor
  model buys.
