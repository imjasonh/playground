// Command tokens passes RequestToken audiences that are constants, one of
// them twice, and one that isn't, for generate's tests. It's never run.
package main

import (
	"context"
	"os"

	"github.com/imjasonh/playground/kube"
)

const octoSTS = "https://octo-sts.dev"

func main() {
	ctx := context.Background()
	_, _, _ = kube.RequestToken(ctx, octoSTS)
	_, _, _ = kube.RequestToken(ctx, "probe")
	_, _, _ = kube.RequestToken(ctx, "")
	_, _, _ = kube.RequestToken(ctx, os.Getenv("AUDIENCE"))
	_, _, _ = kube.RequestToken(ctx, "probe")
}
