// Package host loads Go plugins that export filter.Symbol.
package host

import (
	"bufio"
	"fmt"
	"io"
	"plugin"

	"github.com/imjasonh/playground/go-plugin/filter"
)

// Load opens a plugin built with -buildmode=plugin and calls NewFilter.
// plugin.Open returns the existing plugin when path is already open, and
// does not run init again. Load calls NewFilter on every call.
func Load(path string, cfg filter.Config) (filter.Filter, error) {
	p, err := plugin.Open(path)
	if err != nil {
		return nil, err
	}
	sym, err := p.Lookup(filter.Symbol)
	if err != nil {
		return nil, fmt.Errorf("lookup %s in %s: %w", filter.Symbol, path, err)
	}
	// Lookup returns the function value. Assert the function type.
	// *filter.Constructor is the type used for a variable, and a defined
	// function type is not the type of a function declaration.
	ctor, ok := sym.(filter.Constructor)
	if !ok {
		return nil, fmt.Errorf("lookup %s in %s: type %T, want %T", filter.Symbol, path, sym, filter.Constructor(nil))
	}
	f, err := ctor(cfg)
	if err != nil {
		return nil, fmt.Errorf("new filter %s: %w", path, err)
	}
	if f == nil {
		return nil, fmt.Errorf("new filter %s: nil Filter", path)
	}
	return f, nil
}

// Apply runs filters in order. An error names the filter that returned it.
func Apply(filters []filter.Filter, line string) (string, error) {
	for _, f := range filters {
		next, err := f.Apply(line)
		if err != nil {
			return "", fmt.Errorf("%s: %w", f.Name(), err)
		}
		line = next
	}
	return line, nil
}

// Run reads lines from r, applies filters, and writes each result to w.
func Run(w io.Writer, filters []filter.Filter, r io.Reader) error {
	sc := bufio.NewScanner(r)
	for sc.Scan() {
		out, err := Apply(filters, sc.Text())
		if err != nil {
			return err
		}
		if _, err := fmt.Fprintln(w, out); err != nil {
			return err
		}
	}
	return sc.Err()
}
