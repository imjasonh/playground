# whbiab (Go)

A Go package that records one use of a command-line program in the
[`wehadababyitsaboy`](..) usage-tracking bucket. One call sends one HTTPS
request in the background. The bucket answers `403`, and its usage log keeps
the request.

## Use it in a CLI

Add the module to the CLI's `go.mod`, with a `replace` directive to this
directory, as `gitdb` does:

```bash
cd my-cli
go mod edit \
  -require=github.com/imjasonh/playground/wehadababyitsaboy/go@v0.0.0 \
  -replace=github.com/imjasonh/playground/wehadababyitsaboy/go=../wehadababyitsaboy/go
go mod tidy
```

A CLI whose README tells people to run `go install ...@latest` can't use the
package, because `go install` rejects a module with a `replace` directive.

Call `Track` after the program parses its flags. It starts the request and
returns a function that waits for it. Defer the returned function so that it
runs when the command finishes:

```go
import (
	"context"
	"flag"

	whbiab "github.com/imjasonh/playground/wehadababyitsaboy/go"
)

func main() {
	flag.String("query", "", "SQL to run")
	flag.Parse()
	defer whbiab.Track(context.Background(), "my-cli", whbiab.Flags(flag.CommandLine)...)()
	// ...
}
```

For a CLI with subcommands, pass the subcommand first, then the flags of its
flag set:

```go
defer whbiab.Track(ctx, "my-cli", append([]string{"query"}, whbiab.Flags(fs)...)...)()
```

If the program ends with `os.Exit` or `log.Fatal`, call the returned function
first. Deferred calls don't run on either one.

## What a ping contains

```
https://storage.googleapis.com/wehadababyitsaboy/CLIENT/ARGS?bob=wehadababyitsaboy&arch=ARCH&os=OS&v=VERSION
```

- `CLIENT` is the program name.
- `ARGS` is the subcommand and the names of the flags the user set, joined with
  dots, such as `query.format.offline`. With neither, it's `run`.
- `v` is the module version, or the first 12 characters of the commit that
  built the program, or `dev`.
- `os` and `arch` are `GOOS` and `GOARCH`.
- `ci=1` is added when the `CI` environment variable is set.

The usage log also records the caller's IP address and the `User-Agent`, which
the package sets to `CLIENT/VERSION (whbiab)`.

A ping never contains a flag value or a positional argument, because a value
can be a path, a query, or a token. `Flags` returns only names. Don't pass
anything else that comes from the user. `Track` lowercases each part, replaces
every character outside `a-z`, `0-9`, `-`, and `_` with `-`, and keeps at most
16 parts of 64 characters.

## Turn pings off

Set `DO_NOT_TRACK=1` or `WHBIAB_DISABLE=1`. Any value other than empty or `0`
turns them off.

## Failures and tests

`Track` never returns an error and never prints. A request that fails or takes
more than two seconds is dropped, and the returned function waits no longer
than that.

A test binary sends nothing, so a CLI's tests need no setup. To test the
package against a local server, set `WHBIAB_ENDPOINT` to the server's URL. That
is how this package's own tests run:

```bash
go test -race ./...
```
