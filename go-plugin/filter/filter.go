// Package filter is the contract shared by the host and its plugins.
// Both sides import this package. A second copy of these types in a
// plugin is a different type, and the host's assertion fails.
package filter

import "sync"

// Filter rewrites one line.
// Apply must be safe for concurrent callers.
type Filter interface {
	Name() string
	Apply(line string) (string, error)
}

// Config is the string map passed to a plugin constructor.
type Config map[string]string

// Symbol is the exported constructor every plugin provides.
const Symbol = "NewFilter"

// Constructor is the type of the NewFilter function.
// A function declaration has an unnamed function type. A defined type
// with the same parameters would fail the host's type assertion, so
// this is an alias.
type Constructor = func(Config) (Filter, error)

var (
	mu         sync.Mutex
	registered []string
)

// Register records that a plugin init function ran.
// The host and the plugin share this package's variables, so a call
// from plugin init is visible to the host after Open returns.
// Open can load two plugins at the same time, so Register is safe
// for concurrent callers.
func Register(name string) {
	mu.Lock()
	defer mu.Unlock()
	registered = append(registered, name)
}

// Registered returns the names passed to Register, in call order.
func Registered() []string {
	mu.Lock()
	defer mu.Unlock()
	out := make([]string, len(registered))
	copy(out, registered)
	return out
}
