package main

import (
	"fmt"
	"os"

	"github.com/imjasonh/playground/go-builder/internal/build"
	"github.com/imjasonh/playground/go-builder/internal/cnb"
)

func main() {
	env, err := cnb.LoadBuildEnv(os.Args[1:])
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	if _, err := build.Run(env, build.Options{}); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}
