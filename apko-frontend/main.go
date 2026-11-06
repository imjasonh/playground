// Command apko-frontend is a BuildKit frontend that builds an image from an
// apko configuration file.
//
// BuildKit runs the image as a gateway frontend. With the argument
// "build-layers", the same binary runs inside the build as the step that
// installs packages and writes the image layers.
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
	if len(os.Args) > 1 && os.Args[1] == helperCommand {
		if err := runHelper(ctx, os.Args[2:]); err != nil {
			clog.FromContext(ctx).Fatal("building layers", "error", err)
		}
		return
	}
	if err := grpcclient.RunFromEnvironment(ctx, frontendBuild); err != nil {
		clog.FromContext(ctx).Fatal("running frontend", "error", err)
	}
}
