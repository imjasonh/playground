// Command redact is a Go plugin. NewFilter requires config key word.
package main

import (
	"errors"
	"log/slog"
	"os"
	"strings"

	"github.com/imjasonh/playground/go-plugin/filter"
)

// NewFilter returns a filter that replaces word with ***.
func NewFilter(cfg filter.Config) (filter.Filter, error) {
	word := cfg["word"]
	if word == "" {
		return nil, errors.New("redact: word is required")
	}
	return redactor{word: word}, nil
}

type redactor struct {
	word string
}

func (redactor) Name() string { return "redact" }

func (r redactor) Apply(line string) (string, error) {
	return strings.ReplaceAll(line, r.word, "***"), nil
}

func main() {
	slog.Error("redact is a plugin", "build", "go build -buildmode=plugin -o redact.so .")
	os.Exit(2)
}
