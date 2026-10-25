# Go plugins

This module is a host that loads [Go plugins](https://pkg.go.dev/plugin) and runs them as a chain of line filters. Each plugin is a `package main` built with `-buildmode=plugin`. The host and the plugins import `filter`, so both sides share one constructor type.

## Build and run

To build the sample plugins and the host, run these commands from `go-plugin/`:

```bash
mkdir -p bin
go build -buildmode=plugin -o bin/upper.so ./plugins/upper
go build -buildmode=plugin -o bin/redact.so ./plugins/redact
go build -o bin/host ./cmd/host
printf '%s\n' 'the secret word' | ./bin/host -filter './bin/redact.so?word=secret' -filter ./bin/upper.so
```

The program writes:

```text
THE *** WORD
```

Repeat `-filter` to chain plugins. Flag order is call order. The optional query string is the `filter.Config` map passed to `NewFilter`. `redact` requires `word`.

Plugins need cgo and Linux, FreeBSD, or macOS. Build the host and the plugins with the same Go toolchain and the same build tags. `go test -race` rebuilds the plugins with `-race`, because a race-enabled host refuses a plugin built without it.

## Contract

A plugin exports this function:

```go
func NewFilter(cfg filter.Config) (filter.Filter, error)
```

`filter.Constructor` is an alias of that function type. A defined type with the same parameters is a different type, and `Lookup` then fails the assertion. The function declaration's type is the unnamed function type.

`filter.Filter` has `Name` and `Apply`. Declare that interface in the shared package. A duplicate declaration in the plugin is a different type.

`plugin.Open` runs the plugin's `init` functions before it returns. It does not run `main`. Opening the same path again returns the existing `*plugin.Plugin` and does not run `init` again. The package has no close. The plugin stays in the process until the process exits.

When the file is a Go plugin and its packages fail to initialize, `Open` remembers the error for that path. A later `Open` in the same process returns that error, including after the file is replaced. A missing file is not remembered.

Package-level variables of a shared import are one copy. `plugins/upper` calls `filter.Register` from `init`, and the host reads that list after `Open`.

Load plugins you built with this host. `init` runs inside the host process. A panic in the plugin stops the process.

## Symbol types

`Lookup` returns an `any`. The dynamic type depends on the kind of symbol. [`plugin.Symbol`](https://pkg.go.dev/plugin#Symbol) shows both shapes: `*v.(*int)` for a variable, and `f.(func())` for a function.

For the constructor function, assert the function type:

```go
sym, err := p.Lookup("NewFilter")
ctor := sym.(filter.Constructor)
```

For a variable, assert a pointer to the variable:

```go
sym, err := p.Lookup("V")
n := sym.(*int)
*n = 7
```

For a variable whose type is an interface, assert a pointer to that interface, then dereference it:

```go
sym, err := p.Lookup("Plugin")
f := *sym.(*filter.Filter)
```

For a variable whose type is a struct, `Lookup` returns a pointer to that struct. When the pointer's method set includes the interface, assert the interface:

```go
sym, err := p.Lookup("Hook")
f := sym.(filter.Filter)
```

`plugins/upper` exports all four, and `host/plugin_test.go` checks each assertion.

## Same build

The host and every plugin must be compiled with the same toolchain, the same build tags, and the same flags that change the standard library. `-race` is one of those flags. A dependency imported by both sides must be the same source. A mismatch makes `plugin.Open` return `plugin was built with a different version of package ...`, or the process crashes later.

The [plugin documentation](https://pkg.go.dev/plugin) states that limit. When one build already produces the host and every plugin, a static binary that blank-imports the plugins is the simpler deploy.

`plugin.Open` uses `dlopen` on Linux, FreeBSD, and macOS, and only in a cgo build. Other systems return `plugin: not implemented`. The [race detector](https://go.dev/issue/24245) misses races inside a loaded plugin.

## Programs that load plugins this way

These programs call `plugin.Open` on a file built with `-buildmode=plugin`.

[Tyk Gateway](https://github.com/TykTechnologies/tyk/blob/master/gateway/mw_go_plugin.go) looks up a symbol named in the API definition. [`goplugin.GetHandler`](https://github.com/TykTechnologies/tyk/blob/83c50e77/goplugin/goplugin.go) asserts `func(http.ResponseWriter, *http.Request)`. The gateway build tag is `goplugin`. The [plugin compiler image](https://github.com/TykTechnologies/custom-go-plugin) matches that gateway's Go version. Plugin file names can include the gateway version, `GOOS`, and `GOARCH`.

[KrakenD](https://github.com/devopsfaith/krakend-documentation/blob/master/extending/writing-plugins.md) loads plugins through [Lura](https://github.com/luraproject/lura/blob/master/proxy/plugin/modifier.go). A plugin exports a package-level variable such as `ModifierRegisterer` and implements the registerer interface. The Lura [Makefile](https://github.com/luraproject/lura/blob/master/Makefile) builds the examples with `-buildmode=plugin`. KrakenD's builder image keeps the Go version, glibc, architecture, and shared dependency versions aligned with the gateway. A mismatch surfaces as `plugin was built with a different version of package ...`.

[Zalando Skipper](https://github.com/zalando/skipper/blob/master/plugins.go) walks plugin directories for `.so` files and looks up `InitPlugin`, `InitFilter`, `InitPredicate`, or `InitDataClient`. `InitFilter` is a function the host calls with the plugin's arguments.

These extension systems use a different mechanism.

[hashicorp/go-plugin](https://github.com/hashicorp/go-plugin) starts each plugin as its own process and calls it over RPC. Terraform, Vault, Nomad, Packer, Boundary, and Waypoint use that library. A crash stays in the plugin process, and the plugin binary can be built on its own schedule.

[Traefik](https://github.com/traefik/traefik/blob/master/pkg/plugins/builder.go) loads its Go plugins with the Yaegi interpreter.

Caddy compiles plugins into one binary with [xcaddy](https://github.com/caddyserver/xcaddy).

MOSN's process-plugin client uses hashicorp/go-plugin.

The standard library package fits a host that builds its plugins in the same job and calls them in process. Tyk, KrakenD, and Skipper do that. Tyk and KrakenD publish a builder image so the plugin toolchain matches the gateway.

## Tests

```bash
go test -race ./...
```

On Windows, and in a build with `CGO_ENABLED=0`, the tests that open plugins skip. `go build ./...` still compiles the host and the plugin sources.
