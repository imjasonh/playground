// Command git-remote-ast is a git remote helper that stores blobs as
// tree-sitter AST payloads (see package helper).
package main

import (
	"fmt"
	"os"

	"github.com/imjasonh/playground/ast-remote/internal/helper"
)

func main() {
	if len(os.Args) < 2 {
		fmt.Fprintln(os.Stderr, "usage: git-remote-ast <remote> [<url>]")
		os.Exit(1)
	}
	remote := os.Args[1]
	url := remote
	if len(os.Args) >= 3 {
		url = os.Args[2]
	}
	if err := helper.Run(remote, url, os.Stdin, os.Stdout, os.Stderr); err != nil {
		fmt.Fprintln(os.Stderr, "git-remote-ast:", err)
		os.Exit(1)
	}
}
