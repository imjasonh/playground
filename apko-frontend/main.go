// Command apko-frontend is a BuildKit frontend that builds an image from an
// apko configuration file.
//
// BuildKit runs the image as a gateway frontend. The same binary also runs
// inside the build: with the argument "fetch-apk" as the step that
// downloads and verifies one package, and with "build-layers" as the step
// that installs packages and writes the image layers.
package main

import (
	"log/slog"
	"os"

	"github.com/chainguard-dev/clog"
	"github.com/moby/buildkit/frontend/gateway/grpcclient"
	"github.com/moby/buildkit/util/appcontext"
)

func main() {
	ctx := clog.WithLogger(appcontext.Context(), clog.New(slog.NewTextHandler(os.Stderr, nil)))
	if len(os.Args) > 1 {
		switch os.Args[1] {
		case helperCommand:
			if err := runHelper(ctx, os.Args[2:]); err != nil {
				clog.FromContext(ctx).Fatal("building layers", "error", err)
			}
			return
		case fetchCommand:
			if err := runFetch(ctx, os.Args[2:]); err != nil {
				clog.FromContext(ctx).Fatal("fetching package", "error", err)
			}
			return
		}
	}
	if err := grpcclient.RunFromEnvironment(ctx, frontendBuild); err != nil {
		clog.FromContext(ctx).Fatal("running frontend", "error", err)
	}
}
