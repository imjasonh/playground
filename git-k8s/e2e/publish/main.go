// Command publish adds a version of a Go module to a directory with the
// layout that a module proxy serves, for the end-to-end test. The gitserver
// command's -goproxy flag serves the directory.
package main

import (
	"flag"
	"log"
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
		log.Fatal("set -root and -dir")
	}
	t, err := time.Parse(time.RFC3339, *at)
	if err != nil {
		log.Fatalf("-time: %v", err)
	}
	if err := goproxytest.Publish(*root, *dir, *version, t); err != nil {
		log.Fatal(err)
	}
}
