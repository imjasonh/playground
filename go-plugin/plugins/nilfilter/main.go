// Command nilfilter returns a nil Filter and a nil error.
package main

import (
	"log/slog"
	"os"

	"github.com/imjasonh/playground/go-plugin/filter"
)

// NewFilter returns a nil filter so the host can reject it.
func NewFilter(filter.Config) (filter.Filter, error) {
	return nil, nil
}

func main() {
	slog.Error("nilfilter is a plugin", "build", "go build -buildmode=plugin -o nilfilter.so .")
	os.Exit(2)
}
