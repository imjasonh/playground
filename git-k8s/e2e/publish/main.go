// Command publish adds a version of a Go module to a directory with the
// layout that a module proxy serves, for the end-to-end test. The gitserver
// command's -goproxy flag serves the directory.
package main

import (
	"flag"
	"log/slog"
	"os"
	"time"

	"github.com/imjasonh/playground/git-k8s/internal/goproxytest"
)

func main() {
	root := flag.String("root", "", "directory that the module proxy serves")
	dir := flag.String("dir", "", "directory that holds the module's go.mod and files")
	version := flag.String("version", "", "version to publish, such as v1.0.0")
	at := flag.String("time", "", "the version's time in RFC 3339 format, such as 2020-01-02T03:04:05Z")
	flag.Parse()
	if *root == "" || *dir == "" {
		slog.Error("set -root and -dir")
		os.Exit(1)
	}
	t, err := time.Parse(time.RFC3339, *at)
	if err != nil {
		slog.Error("parse -time", "error", err)
		os.Exit(1)
	}
	if err := goproxytest.Publish(*root, *dir, *version, t); err != nil {
		slog.Error("publish", "error", err)
		os.Exit(1)
	}
}
