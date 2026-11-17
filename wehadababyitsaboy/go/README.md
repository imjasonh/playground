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

The package works with [cobra](https://github.com/spf13/cobra). Run the root
command through `whbiab.Execute` rather than calling `Execute` on the command.
The ping starts after cobra parses the flags and before the command's `Run`
function, and `Execute` waits for it before returning:

```go
import (
	"context"
	"os"

	whbiab "github.com/imjasonh/playground/wehadababyitsaboy/go"
	"github.com/spf13/cobra"
)

func main() {
	root := &cobra.Command{Use: "my-cli"}
	root.AddCommand(&cobra.Command{
		Use: "query",
		RunE: func(cmd *cobra.Command, args []string) error {
			return nil
		},
	})
	if err := whbiab.Execute(context.Background(), root); err != nil {
		os.Exit(1)
	}
}
```

`CLIENT` is the root command's name. `ARGS` is the subcommands under the root
and the names of the flags the user set, including persistent flags inherited
from a parent. A ping never contains a flag value or a positional argument.
`Execute` sends nothing for help, shell completion, or arguments that fail to
parse.

`os.Exit` and `log.Fatal` skip the wait, so call them only after `Execute`
returns.

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
can be a path, a query, or a token. `Execute` lowercases each part, replaces
every character outside `a-z`, `0-9`, `-`, and `_` with `-`, and keeps at most
16 parts of 64 characters.

## Turn pings off

Set `DO_NOT_TRACK=1` or `WHBIAB_DISABLE=1`. Any value other than empty or `0`
turns them off.

## Failures and tests

`Execute` never fails because of a ping and never prints about one. A request
that fails or takes more than two seconds is dropped, and `Execute` waits no
longer than that.

A test binary sends nothing, so a CLI's tests need no setup. To test the
package against a local server, set `WHBIAB_ENDPOINT` to the server's URL. That
is how this package's own tests run:

```bash
go test -race ./...
```
