// Command host reads lines and rewrites them with Go plugins.
package main

import (
	"log/slog"
	"os"

	"github.com/imjasonh/playground/go-plugin/host"
)

func main() {
	if err := host.RunCLI(os.Args[1:], os.Stdin, os.Stdout); err != nil {
		slog.Error("host", "err", err)
		os.Exit(1)
	}
}
