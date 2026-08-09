# Design: running arm64 containers on an iOS host

> Status: **exploration** — no code yet. This doc maps the option space for an
> iOS experiment where the user names a container image and the app runs it.
> It ends with a recommended architecture (§6) and a phased plan (§7).
>
> Scope: the **Playground** iOS app (`ios/`), delivered via TestFlight. Anything
> that requires sideloading, TrollStore, or a jailbreak is out of scope for
> shipping, but is documented in §5.5 because it sets the performance ceiling.

## 0. The short version

| Question | Answer |
|----------|--------|
| Can iOS run a container the way `container`/Docker does on macOS? | **No.** No Hypervisor/Virtualization framework, no namespaces, no cgroups, no `mount`, no `fork`/`exec`. |
| Can the app execute the image's arm64 ELF binaries directly? | **No.** All executable pages must be signed by Apple. Same-ISA does not help. |
| So the guest must be *interpreted*? | Yes — **unless** you route it through WebKit, the one process on the device allowed to JIT third-party code. |
| Is there a legal, no-entitlement way to run an arbitrary arm64 image on-device? | **Yes:** emulate in WebAssembly inside a `WKWebView`. QEMU's wasm backend emits wasm at runtime, and WebKit JIT-compiles it. |
| Is it fast? | No. Expect "usable shell", not "usable workload". Memory is capped near 300 MB–1 GB by the WebContent jetsam budget. |
| What's the recommended build? | **Native OCI client + loopback HTTP server + WKWebView running container2wasm.** Swift pulls and unpacks the image; WebKit is used purely as the CPU. See §6. |

The one-sentence framing: **on iOS you cannot bring the code to the CPU, so you
bring a CPU to the code — and the only CPU you're allowed to synthesize at
runtime lives inside WebKit.**

## 1. What "run a container" decomposes into

It is worth separating the parts, because iOS blocks exactly one of them.

| Part | Needs | iOS status |
|------|-------|-----------|
| Resolve a reference, auth to a registry, pull manifest + config + layers | HTTPS, JSON, tar, gzip/zstd | **Fine.** Plain `URLSession` work. |
| Materialize a root filesystem (layer stacking, whiteouts, hardlinks) | File I/O | **Fine**, in the app container, as long as you emulate the union semantics yourself. |
| Isolate: namespaces, cgroups, pivot_root, overlayfs | Linux kernel | **Absent.** Not "restricted" — the kernel is XNU; these concepts don't exist. |
| **Execute the image's binaries** | Run downloaded arm64 machine code | **Blocked.** This is the whole problem. |
| Networking for the guest | Sockets | Fine natively; needs a bridge into whatever sandbox the guest runs in. |

Everything except execution is ordinary app engineering. So the rest of this doc
is about execution.

## 2. The hard platform constraints

### 2.1 No unsigned native code, ever

iOS enforces code signing on every executable page, and W^X on top of it. An app
cannot `mmap` anonymous memory `PROT_EXEC`, cannot `dlopen` a downloaded dylib,
and cannot `exec` a downloaded binary. The Apple Developer Program License
Agreement §3.3.1(B) says the same thing contractually.

This is *ISA-independent*. Running arm64 guest code on an arm64 host buys you
nothing: the bytes were not signed by Apple, so they cannot be executed. This is
the single fact that shapes every option below.

### 2.2 JIT is not available to us

- `com.apple.security.cs.allow-jit` is **macOS-only** (Hardened Runtime).
- iOS 26 added a real JIT path — the `JITAuthorizer` class plus
  `com.apple.developer.kernel.allow-jit`. It is **not accepted in App Store
  submissions**; emulator projects that adopted it (e.g. Provenance) ship it
  only in their jailbreak/sideload variants. Our builds are App Store–signed
  distribution builds going to TestFlight, so this is unavailable.
- The debugger-attach tricks (AltJIT, JitStreamer, StikDebug) require
  `get-task-allow`, which distribution-signed TestFlight builds do not have.
- `BrowserEngineKit` grants JIT, but only under the EU/Japan alternative-browser-engine
  entitlements, which require Apple approval and a browser as the app's purpose.

**Exception that matters:** `WKWebView` renders in the out-of-process WebContent
process, which is Apple-signed and *does* hold the JIT entitlement. In-process
`JavaScriptCore` (`JSContext`) is interpreter-only; `WKWebView` is not. That
asymmetry is the entire basis for the recommended design.

### 2.3 No hypervisor, no virtualization — still true after WWDC26

`Hypervisor.framework` and `Virtualization.framework` are macOS-only, confirmed
repeatedly by Apple engineers on the developer forums. Apple's own container
stack (`apple/containerization`, the `container` CLI, and the WWDC26 "container
machines" feature) is built on `Virtualization.framework` and is macOS-only —
WWDC26 brought it to macOS 27, not to iPadOS 27. M-series iPads have the silicon
capability; iPadOS does not expose it. UTM's hypervisor build exists only for
TrollStore/jailbroken devices.

So: **no lightweight VM per container, on any shipping iOS/iPadOS version.**

### 2.4 No Linux process model

No `fork`, no `exec` of arbitrary binaries, no `clone` namespaces, no
`/dev/fuse`, no `mount`. Any multi-process guest (`sh` spawning `ls`) has to be
modeled *inside* the emulator, either by emulating a real kernel (full-system
emulation) or by reimplementing the process model in userspace (iSH's approach).

### 2.5 Memory is the binding constraint, and there are two separate budgets

- **App process:** governed by jetsam; query with `os_proc_available_memory()`.
  It can be raised with `com.apple.developer.kernel.increased-memory-limit`, but
  that is a *restricted* entitlement: it must be enabled as a capability on the
  App ID and flow through the provisioning profile. In this repo that means a
  **signing re-bootstrap** (see `ios/AGENTS.md`) — not free.
- **WebContent process:** a *separate*, lower budget that you cannot raise —
  Apple's answer on the forums is literally "it is not possible to increase the
  limit". Practical figures reported in the wild are roughly 200–450 MB on
  older iPhones and ~1 GB on recent ones. Large `WebAssembly.Memory` maxima are
  a known instant-OOM trigger on iOS.

Consequence: a webview-hosted guest realistically gets **128–256 MB of guest
RAM**. That runs Alpine and busybox comfortably. It does not run your CI image.

### 2.6 Background execution

A container is a long-running process; iOS is not. Backgrounding suspends the
app within seconds unless a background mode applies (none of the legitimate ones
fit "run a container"). The guest must be pausable and resumable, and the UX has
to treat "app went to background" as a suspend point.

### 2.7 App Review, honestly assessed

- **2.5.2** forbids downloading/executing code that "introduces or changes
  features or functionality of the app."
- **4.7** carves out mini apps, HTML5/JS content, and emulators, and **4.7.2**
  (clarified November 2025) says such software may not "extend or expose native
  platform APIs or technologies" without Apple's permission.

The precedents cut in our favor: **iSH** (x86 Linux userland, App Store),
**UTM SE** (QEMU with a threaded interpreter, App Store after an initial
rejection), plus the retro-emulator category. The consistent pattern is that
downloaded content is treated as *data for an interpreter that shipped in the
reviewed binary*. Two design rules follow, and they're cheap to honor:

1. **Ship the emulator in the app bundle.** Never download the runtime. Only the
   user's image is fetched at runtime — that's data.
2. **Keep native bridges narrow.** Every native capability you hand to the guest
   moves you toward the 4.7.2 line.

Also relevant: this app ships to **TestFlight**. Internal testers (App Store
Connect users on the team) do not go through Beta App Review at all, so a
first cut carries essentially no review risk. External TestFlight and the App
Store do.

## 3. Where can guest instructions actually execute?

Given §2.1, there are exactly four places a guest instruction can be executed,
and this enumeration is what makes the option space finite.

| # | Executor | Signed code doing the work | JIT? |
|---|----------|---------------------------|------|
| 1 | Another machine | remote kernel | n/a — native speed |
| 2 | **WebKit's wasm engine** | Apple's WebContent process | **Yes** (BBQ/OMG) |
| 3 | An interpreter compiled into our app | our reviewed binary | No |
| 4 | The bare CPU | — | Requires entitlements we cannot get |

Everything below is one of these four.

## 4. Option A — remote runtime (the app is a client)

Pull and run on something that is not the phone: a cloud sandbox, a Mac running
Apple's `container`, a k8s cluster, a Fly Machine. The app does image selection,
log/TTY streaming over WebSocket, and lifecycle UI.

- **Speed:** native. **Fidelity:** perfect. **Effort:** low.
- **Cost:** it isn't running on the device, which is the interesting part of the
  question. Also needs infrastructure and credentials.

Worth building eventually as a "remote" backend behind the same UI, because it's
the only mode where a real workload finishes. Not the interesting answer.

## 5. On-device options

### 5.1 Option B — WebKit-hosted emulation (container2wasm + QEMU Wasm)

This is the one that actually satisfies "name an image, run it" on-device.

[container2wasm](https://github.com/container2wasm/container2wasm) (`c2w`) runs
containers on wasm by shipping a CPU emulator compiled to wasm plus a Linux
kernel and `runc`. Emulators: Bochs (x86_64), TinyEMU (riscv64), and **QEMU Wasm
for aarch64** (`c2w --to-js --target-arch=aarch64`, the default emulator for
aarch64 guests in the browser).

The clever part, and the reason this beats every native option on speed:
[QEMU Wasm](https://github.com/ktock/qemu-wasm) adds a **TCG backend that emits
WebAssembly**. Translation blocks start on TCI (the interpreter); blocks that
execute enough times (~1000) are compiled into a wasm module, instantiated via
`WebAssembly.Module`/`WebAssembly.Instance`, and called through Emscripten's
`addFunction`. So there *is* dynamic binary translation with a real optimizing
compiler behind it — WebKit's — and no iOS entitlement is involved, because what
we generate at runtime is wasm, not machine code. Upstreaming is in progress:
32-bit TCI landed in QEMU 10.1, and the wasm64 TCG backend was at v4 on
qemu-devel in January 2026.

What has to be true on iOS:

- **Cross-origin isolation.** QEMU Wasm uses Emscripten pthreads, so it needs
  `SharedArrayBuffer`, which needs `crossOriginIsolated`, which needs
  `Cross-Origin-Opener-Policy: same-origin` + `Cross-Origin-Embedder-Policy:
  require-corp` on the document. iOS `WKWebView` **does not honor** the
  service-worker header shims (`mini-coi.js`) that work in Safari. It also will
  not grant a secure context to a custom `WKURLSchemeHandler` scheme. The
  workaround that does work: **serve the page from an in-app loopback HTTP
  server on `127.0.0.1`**, which is a potentially-trustworthy origin, and set
  the headers there. Add an ATS exception for localhost
  (`NSExceptionAllowsInsecureHTTPLoads`, scoped to `localhost`).
- **Safari/WebKit quirks.** c2w has already shipped a fix for a Safari-specific
  stack-size failure when running aarch64 guests, and the wasm64 QEMU backend
  carries a compatibility option for Safari's smaller wasm address limit. Both
  signal that Safari is a supported-but-second-class target: expect to spend
  real time here.
- **Memory.** §2.5. Budget the guest at 128–256 MB and set an explicit
  `WebAssembly.Memory` maximum rather than letting it grow.

**Running an image the user typed, without a build step.** `c2w` normally bakes
one image into one wasm artifact, which is useless for "name any image". The
`extras/imagemounter` path is what we want: `c2w --external-bundle` produces a
Linux+`runc` wasm VM with **no** image inside, and `imagemounter.wasm` pulls an
image and exposes its rootfs to the VM over **9p**. Its documented limitations
are registry **auth is unsupported**, the registry must send **CORS** headers
(no public registry does), and **gzip layers decompress slowly inside the wasm
VM**.

All three of those limitations dissolve on iOS, which is the key insight of §6:
a native app is not a browser. Swift can authenticate to any registry, and can
serve the unpacked result to its own webview from localhost.

### 5.2 Option C — native wasm interpreter, for wasm-native images

If the image is built for `wasip1`/`wasm` rather than `linux/arm64`, no CPU
emulation is needed at all: unpack the image, take the `.wasm` entrypoint, and
run it in an interpreter linked into the app — [WasmKit](https://github.com/swiftwasm/WasmKit)
(pure Swift), wasm3, or WAMR in interpreter mode. No webview, no COOP/COEP, no
WebContent memory cap, full native file and network integration, and it is
squarely inside the "interpreter shipped in the reviewed binary" pattern.

The catch is obvious: it only runs images someone built for wasm. It's a real
and cheap capability, but it is not "run this arm64 image."

### 5.3 Option D — native CPU interpreter (the iSH / UTM SE approach)

Compile an emulator into the app and interpret guest instructions natively.

- **iSH** interprets x86 in a threaded-code interpreter (arrays of gadget
  function pointers, each tail-calling the next; ~3–5× faster than switch
  dispatch) and translates Linux syscalls to Darwin, reimplementing the process
  model in userspace. It runs Alpine, and it is on the App Store.
- **UTM SE** is QEMU with TCTI, a tiny-code threaded interpreter instead of TCG
  JIT. Its own maintainers call it the "Slow Edition"; community measurements
  put it around 9–10× slower than the JIT build.

Advantages over Option B: the app's own (raisable) memory budget instead of the
WebContent one, native filesystem and networking, and no webview plumbing.

Disadvantages: it is strictly interpreted — no dynamic translation is possible,
by §2.1 — so it is the **slowest** option, while also being the **most** work
(porting a large C emulator into the XcodeGen project, or writing an
arm64-on-arm64 interpreter plus a Linux syscall layer from scratch). For an
arm64 guest on an arm64 host, interpreting is a particularly bitter pill.

### 5.4 Option E — off-Store paths (for calibration only)

Sideloaded builds with `get-task-allow` plus a JIT enabler (AltJIT, StikDebug,
JitStreamer) run full UTM with TCG JIT. TrollStore or a jailbreak on M-series
iPads can reach `com.apple.private.hypervisor` and run *actual virtualization*
at near-native speed — that is how people run real Linux VMs on iPads today.

Not shippable through TestFlight. Useful as a benchmark upper bound, and useful
context for anyone who asks "why is this so slow."

### 5.5 Comparison

| | A. Remote | B. WebKit + c2w | C. Native wasm | D. Native interpreter | E. Off-Store |
|---|---|---|---|---|---|
| Arbitrary `linux/arm64` image | ✅ | ✅ | ❌ | ✅ | ✅ |
| Runs on-device | ❌ | ✅ | ✅ | ✅ | ✅ |
| Dynamic translation (JIT) | n/a | ✅ (wasm via WebKit) | n/a | ❌ | ✅ |
| Ships via TestFlight | ✅ | ✅ | ✅ | ✅ | ❌ |
| New entitlement / bootstrap | ❌ | ❌ | ❌ | only if raising memory | n/a |
| Guest RAM ceiling | host | ~128–256 MB | app budget | app budget | device RAM |
| Relative speed | 1× | slow | fast (wasm only) | slowest | near-native |
| Effort | low | medium | low | very high | n/a |

## 6. Recommended architecture

**Native app as the container plumbing; WebKit as the CPU.**

```
┌─ Playground app (Swift, our signed binary) ─────────────────────────┐
│                                                                     │
│  1. OCI client         registry v2 + token auth, manifest lists,    │
│                        platform select (linux/arm64), blob pull     │
│  2. Layer store        verify digests, gunzip/zstd natively,        │
│                        write out an OCI Image Layout on disk        │
│  3. Loopback server    127.0.0.1, serves:                           │
│                          • bundled runtime assets (wasm, JS, kernel)│
│                          • the unpacked image as OCI Image Layout   │
│                        with COOP/COEP/CORP + CORS headers           │
│  4. WKWebView  ─────────────────────────────────────────────────┐   │
│       │        loads http://127.0.0.1:<port>/?image=…           │   │
│       │        ┌────────────────────────────────────────────┐   │   │
│       │        │ imagemounter.wasm  → rootfs over 9p        │   │   │
│       │        │ c2w --external-bundle VM (Linux + runc)    │   │   │
│       │        │ QEMU Wasm aarch64: TCI → wasm TB compile   │   │   │
│       │        │   ↑ WebKit BBQ/OMG JIT-compiles those TBs  │   │   │
│       │        │ xterm-pty terminal UI                      │   │   │
│       │        └────────────────────────────────────────────┘   │   │
│  5. SwiftUI chrome: image field, run/stop, logs, resource meter ┘   │
└─────────────────────────────────────────────────────────────────────┘
```

Why this shape specifically:

- **It erases c2w's three browser limitations.** Registry auth: Swift does it,
  so Docker Hub / GHCR / private registries all work. CORS: irrelevant, because
  the webview only ever talks to our own loopback origin — no `cors-proxy`
  needed. Slow in-VM gunzip: we decompress natively and serve an already-unpacked
  OCI layout.
- **It gets the only JIT on the device** without any entitlement, because the
  runtime-generated code is wasm and WebKit compiles it.
- **It keeps the review story clean** (§2.7): the emulator is bundled and
  reviewed; only the image is fetched; the native surface exposed to the guest
  is one localhost HTTP origin.
- **It's incrementally testable.** Phase 1 has no webview at all and is pure
  unit-testable Swift.

Open engineering questions to settle during Phase 2, in rough risk order:

1. **Asset size.** A wasm `qemu-system-aarch64` plus kernel and initramfs is
   large. Measure it first — if the bundle grows unacceptably, the options are
   On-Demand Resources (which weakens the "runtime ships in the binary" story,
   so prefer not to) or a smaller emulator/kernel configuration.
2. **Does WebKit reach the OMG tier in a third-party `WKWebView`?** WKWebView
   embeds were historically BBQ-only, and reports differ across iOS releases.
   BBQ-only would cost a large constant factor. Measure on device.
3. **Thread count.** Emscripten pthreads under a WebContent memory cap; MTTCG
   may need to be constrained or disabled.
4. **Guest networking.** c2w offers `?net=browser` (a gvisor-tap-vsock stack
   forwarding via `fetch`) or a WebSocket delegate to a host-side stack — the
   latter maps naturally to a native `NWListener`, giving real TCP. Note this is
   the change most likely to attract 4.7.2 attention; keep it opt-in and
   default-off.
5. **Suspend/resume** across app backgrounding (§2.6).

## 7. Phased plan

### 7.0 Where this stands

**The kill-switch passed.** A page served by an in-app loopback HTTP server on
`127.0.0.1`, with `Cross-Origin-Opener-Policy: same-origin` and
`Cross-Origin-Embedder-Policy: require-corp`, is cross-origin isolated inside a
`WKWebView`: `crossOriginIsolated === true`, `SharedArrayBuffer` exists, and a
shared `WebAssembly.Memory` constructs. That is asserted in CI by
`ContainerLabIsolationProbeTests` and re-checkable on a device from the
experiment's Runtime section. Option B is therefore live, and the Option C/D
fallbacks stay on the shelf.

Measured on the simulator, not yet on a device — same WebKit, different process
limits, so the memory ceiling still needs a device run.

| Phase | State |
|-------|-------|
| 1 — native OCI pull | Done: reference parsing, Bearer auth, index → platform, digest-verified blobs, native gunzip, OCI layout on disk |
| 2 — loopback + isolation | Done: server, headers, probe, all green in CI |
| 3 — c2w runtime | In progress: `container-runtime.yml` builds it; not yet bundled |
| 4 — follow-on | Not started |

Two things worth writing down for whoever picks this up:

- **Layer decompression is free verification.** Inflating layers natively means
  the resulting digest *is* the `diff_id` the image config already published,
  so the rewritten manifest checks itself against the original config. A
  mismatch aborts the pull.
- **c2w v0.8.4 cannot build out of the box**, and both of its failures are
  network fetches inside a build that otherwise runs for tens of minutes, so
  they are worth patching rather than retrying. Its embedded Dockerfile clones
  build assets from the project's old home, `github.com/ktock/container2wasm`,
  which no longer carries the release tags (`Remote branch v0.8.4 not found`),
  and it fetches zlib from `zlib.net/fossils`, which answered a GitHub runner
  with something `tar` read as "not in gzip format".
  `.github/scripts/prepare-c2w-build.sh` sidesteps both: it hands buildx a
  pinned local checkout as the `assets` context (`c2w --assets`) so there is no
  clone, and patches the Dockerfile (`c2w --show-dockerfile` →
  `c2w --dockerfile`) to take zlib from its byte-identical GitHub release.
- **Building the emulator is not the same as it working.** The workflow serves
  the converted output from a cross-origin-isolated origin and boots it in
  headless Chromium, waiting for alpine's prompt and then asking the guest
  `uname -sm`. It drives the very page the app bundles, so the page is under
  test too. Chromium is not WebKit, but everything it exercises — the isolation
  headers, the wasm, xterm-pty, the emscripten glue — is shared, which leaves
  only WebKit's own behaviour to confirm on a device.

**Phase 1 — "specify an image" (native, no emulation).** A `ContainerLab`
experiment under `ios/Sources/Experiments/`: type a reference, resolve it, pull
manifest/config, pick the `linux/arm64` platform from an index, list layers with
sizes and digests, show entrypoint/cmd/env, and materialize an OCI Image Layout
on disk. Registry auth, digest verification, and layer/whiteout stacking are all
plain types with unit tests in `ios/Tests/PlaygroundTests/`. No new Bundle ID,
no entitlement, no signing bootstrap. This is genuinely useful on its own and
de-risks half the work.

**Phase 2 — loopback + WebKit spike.** Loopback server with COOP/COEP; prove
`crossOriginIsolated === true` and `SharedArrayBuffer` in a `WKWebView` before
integrating anything else. This phase either validates or kills Option B,
cheaply. It validated it (§7.0).

**Phase 3 — c2w runtime.** Build the emulator (`c2w --to-js
--target-arch=aarch64`, which is QEMU Wasm under Emscripten), bundle it under
`ios/ContainerRuntime/`, wire xterm-pty to the console, and boot
`arm64v8/alpine`. The build needs Docker + buildx and compiles both QEMU and a
Linux kernel, so it lives in its own workflow and its output is fetched rather
than committed. Then move from the baked-in image to `--external-bundle` +
`imagemounter.wasm` reading the Phase 1 layout, which is what turns "boots
alpine" into "boots the image you named". Measure boot time, steady-state
speed, and peak WebContent memory.

**Phase 4 — choose the follow-on** based on Phase 3 numbers: guest networking,
a `wasip1` fast path (Option C — cheap once the OCI client exists), or a remote
backend (Option A) behind the same UI for workloads that need to finish.

A sensible early kill-switch: if Phase 2 cannot get `crossOriginIsolated` in a
`WKWebView`, Option B is dead, and the honest fallback is Option C for wasm
images plus Option A for everything else — because Option D buys arbitrary-image
support at the price of the slowest possible execution and the most work.

## 8. What will never work

For the record, so nobody re-litigates these:

- Native execution of the image's binaries, on any distribution channel Apple
  controls. Not a bug, not a workaround away.
- `Virtualization.framework` / Apple `container` / `containerization` on iOS.
- Real Linux isolation primitives (namespaces, cgroups, overlayfs) on XNU. What
  we call "the container" is a guest inside an emulator; the isolation is the
  emulator's, not the kernel's.
- Running the guest in the background indefinitely.
- App Store–signed JIT, including the iOS 26 `JITAuthorizer` path.

## 9. References

Platform and policy

- App Review Guidelines, [2.5.2 and 4.7](https://developer.apple.com/app-store/review/guidelines/); [November 2025 revisions](https://developer.apple.com/news/?id=ey6d8onl) (4.7, 4.7.2)
- [`com.apple.developer.kernel.increased-memory-limit`](https://developer.apple.com/documentation/BundleResources/Entitlements/com.apple.developer.kernel.increased-memory-limit) — restricted; needs App ID capability
- Apple Developer Forums: [Hypervisor/Virtualization are macOS-only](https://developer.apple.com/forums/thread/747029); [WKWebView memory budget cannot be raised](https://developer.apple.com/forums/thread/133449)
- WWDC26: [Discover container machines](https://developer.apple.com/videos/play/wwdc2026/389/) (macOS); [iPadOS 27 guide](https://developer.apple.com/wwdc26/guides/ipados/) (no container/VM support)

Emulation and runtimes

- [container2wasm](https://github.com/container2wasm/container2wasm) and [`extras/imagemounter`](https://github.com/container2wasm/container2wasm/tree/main/extras/imagemounter)
- [QEMU Wasm](https://github.com/ktock/qemu-wasm); [wasm64 TCG backend v4 on qemu-devel, Jan 2026](https://lists.nongnu.org/archive/html/qemu-devel/2026-01/msg04985.html)
- [UTM / UTM SE](https://github.com/utmapp/UTM) and its [iOS install matrix](http://docs.getutm.app/installation/ios/)
- [iSH](https://github.com/ish-app/ish) — threaded-code interpreter + syscall translation
- [WasmKit](https://github.com/swiftwasm/WasmKit) — pure-Swift wasm interpreter
- [Apple Containerization](https://github.com/apple/containerization) — macOS-only, but a good reference for OCI handling in Swift
