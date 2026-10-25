// Command upper is a Go plugin. Build it with:
//
//	go build -buildmode=plugin -o upper.so .
//
// plugin.Open does not call main.
package main

import (
	"log/slog"
	"os"
	"strings"

	"github.com/imjasonh/playground/go-plugin/filter"
)

func init() {
	filter.Register("upper")
	Inited = true
}

// Inited is set from init. The host observes it after Open returns.
var Inited bool

// V is a plugin variable. Lookup returns *int.
var V = 1

// F returns V. Lookup returns func() int, which is the function value.
func F() int { return V }

// Plugin is an interface variable. Lookup returns *filter.Filter.
var Plugin filter.Filter = upper{}

// Hook is a concrete variable. Lookup returns *hook, and *hook implements filter.Filter.
var Hook hook

type hook struct{}

func (hook) Name() string { return "hook" }

func (hook) Apply(line string) (string, error) { return line, nil }

// NewFilter is the constructor the host looks up.
func NewFilter(filter.Config) (filter.Filter, error) {
	return upper{}, nil
}

type upper struct{}

func (upper) Name() string { return "upper" }

func (upper) Apply(line string) (string, error) {
	return strings.ToUpper(line), nil
}

// main exists so `go build ./...` accepts the package. The host does not call it.
func main() {
	slog.Error("upper is a plugin", "build", "go build -buildmode=plugin -o upper.so .")
	os.Exit(2)
}
