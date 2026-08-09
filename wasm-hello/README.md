# wasm-hello

A hello-world Go HTTP service that is **distributed as an OCI artifact and run
as a WebAssembly module** — the payload for the iOS *Wasm Service* experiment,
where a phone pulls it from a registry and serves it on a real TCP port.

The handler itself is unremarkable `net/http`. That is the point: nothing in
[`handler/`](handler/) knows it will end up in wasm.

```
go build ./...            # a normal Go web server (main.go)
GOOS=wasip1 GOARCH=wasm \
  go build -buildmode=c-shared -o hello.wasm .   # the same handler, as a module
```

## Why a reactor module, not a program

`-buildmode=c-shared` (Go 1.24+) makes this a **reactor**: the host calls
`_initialize` once to start the Go runtime, then calls into exported functions
for as long as it likes. The Go scheduler, the heap, and the request counter in
`handler.Service` all survive between requests, so a phone pays the runtime
startup cost once rather than per request.

A wasip1 module cannot `accept()` — there are no sockets in the sandbox and no
`wasi-sockets` in preview 1 — so the **host owns the listener** and the guest
owns the request. That split is also what makes the module runnable by a
non-JIT interpreter inside an iOS app, which is the only kind of runtime an App
Store app is allowed to have.

## The host ABI

Three exports and the module's `memory`, versioned so a host can refuse a
module it does not understand:

| Export | Signature | Meaning |
|--------|-----------|---------|
| `http_abi_version` | `() -> i32` | `1` for the ABI below |
| `http_alloc` | `(size: i32) -> i32` | Reserve `size` bytes; returns the offset to write them at |
| `http_handle` | `(offset: i32, length: i32) -> i64` | Serve one request; returns `offset << 32 \| length` of the response |

Both the request and the response are **raw HTTP/1.1 bytes**. The host already
has request bytes off a socket and needs response bytes to write back, so
passing them through unchanged avoids inventing a second wire format, and lets
a guest in any language implement this with an off-the-shelf HTTP parser.

One exchange, as the host performs it:

1. `offset = http_alloc(len(request))`
2. write the request bytes into the module's memory at `offset`
3. `packed = http_handle(offset, len(request))`
4. read `packed & 0xffffffff` bytes at `packed >> 32` — the response

The response buffer stays valid until the next `http_handle`, which is why
there is no `free`: the host reads it out before making another call.
`http_handle` insists on being handed exactly the region `http_alloc` returned,
and answers `400` otherwise — the guest then slices a buffer it already owns
rather than turning a host-supplied integer into a pointer to anywhere.

## Routes

| Route | Response |
|-------|----------|
| `GET /` | Greeting, Go version, `GOOS/GOARCH`, uptime, request count |
| `GET /healthz` | `ok` |
| `GET /info` | The same as JSON, plus goroutine count |
| `ANY /echo` | The request, reflected back |

`/info`'s request count is the useful one when you are looking at a phone: it
only keeps climbing if the instance really is being reused.

## Run it

```bash
cd wasm-hello
go run . --addr 127.0.0.1:8080     # native
curl 127.0.0.1:8080/info
```

Under a wasm runtime, with the reactor's entry point and a host that speaks the
ABI above:

```bash
GOOS=wasip1 GOARCH=wasm go build -buildmode=c-shared -o hello.wasm .
```

`wasmtime run` will not do anything useful with it — there is no `_start` to
run and no listener to connect to. [`wasm_roundtrip_test.go`](wasm_roundtrip_test.go)
is the runnable example: it builds the module and drives it through
[wazero](https://wazero.io) exactly as the iOS host does.

## Test

```bash
go test ./...
```

`wire/` is tested natively; the root test builds the wasip1 module and performs
real HTTP exchanges through it, asserting the export names and the packed
return value so the ABI cannot drift away from the Swift host that decodes it.

## Distribution

CI ([`wasm-hello.yml`](../.github/workflows/wasm-hello.yml)) pushes the module
to GHCR as an OCI artifact on every push to `main`:

```
ghcr.io/imjasonh/playground/wasm-hello:latest
```

`artifactType` is `application/vnd.wasm.config.v0+json` and the single layer is
`application/wasm`; there is no root filesystem, because there is no container
here — OCI is only the delivery mechanism.

```bash
oras pull ghcr.io/imjasonh/playground/wasm-hello:latest
crane manifest ghcr.io/imjasonh/playground/wasm-hello:latest
```

> A package GHCR publishes for the first time is **private**. Anonymous pulls —
> which is what the phone does — need it flipped to public once, under the
> repository's *Packages* settings. Until then the app reports a 401 rather
> than pretending.
