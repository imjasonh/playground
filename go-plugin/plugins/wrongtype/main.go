// Command wrongtype exports NewFilter with a type the host rejects.
package main

import (
	"log/slog"
	"os"
)

// NewFilter has the constructor's name and a different type.
func NewFilter(n int) int { return n }

func main() {
	slog.Error("wrongtype is a plugin", "build", "go build -buildmode=plugin -o wrongtype.so .")
	os.Exit(2)
}
