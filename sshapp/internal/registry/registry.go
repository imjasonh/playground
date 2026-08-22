// Package registry lists sshapps and lets a session pick one.
// The mux serves this inline (always-on); it is not a separate backend app.
package registry

import (
	"bufio"
	"errors"
	"fmt"
	"io"
	"strconv"
	"strings"
)

// ErrCanceled means the user quit the menu without choosing.
var ErrCanceled = errors.New("canceled")

// Entry is one registered app the mux can route to.
type Entry struct {
	Name string
	// Summary is optional one-line help shown in the menu.
	Summary string
}

// Catalog is the set of apps the mux knows about.
type Catalog struct {
	Apps []Entry
}

// Names returns app names in catalog order.
func (c Catalog) Names() []string {
	out := make([]string, 0, len(c.Apps))
	for _, a := range c.Apps {
		out = append(out, a.Name)
	}
	return out
}

// Lookup returns the entry with the given name, if any.
func (c Catalog) Lookup(name string) (Entry, bool) {
	for _, a := range c.Apps {
		if a.Name == name {
			return a, true
		}
	}
	return Entry{}, false
}

// FromNames builds a Catalog from bare app names (no summaries).
func FromNames(names []string) Catalog {
	apps := make([]Entry, 0, len(names))
	for _, n := range names {
		n = strings.TrimSpace(n)
		if n == "" {
			continue
		}
		apps = append(apps, Entry{Name: n})
	}
	return Catalog{Apps: apps}
}

// WriteList prints the registry to w.
func (c Catalog) WriteList(w io.Writer) error {
	if len(c.Apps) == 0 {
		_, err := fmt.Fprintln(w, "no apps registered")
		return err
	}
	if _, err := fmt.Fprintln(w, "available apps:"); err != nil {
		return err
	}
	for i, a := range c.Apps {
		line := fmt.Sprintf("  %d) %s", i+1, a.Name)
		if a.Summary != "" {
			line += "  -  " + a.Summary
		}
		if _, err := fmt.Fprintln(w, line); err != nil {
			return err
		}
	}
	return nil
}

// Pick prompts on w and reads a selection from r.
// Accepts a 1-based index or an app name. Empty input or "q"/"quit" cancels.
func (c Catalog) Pick(r io.Reader, w io.Writer) (Entry, error) {
	if len(c.Apps) == 0 {
		return Entry{}, fmt.Errorf("no apps registered")
	}
	if err := c.WriteList(w); err != nil {
		return Entry{}, err
	}
	if _, err := fmt.Fprint(w, "select number or name (q to quit): "); err != nil {
		return Entry{}, err
	}
	line, err := bufio.NewReader(r).ReadString('\n')
	if err != nil && !errors.Is(err, io.EOF) {
		return Entry{}, err
	}
	choice := strings.TrimSpace(line)
	if choice == "" || choice == "q" || choice == "quit" {
		return Entry{}, ErrCanceled
	}
	if n, err := strconv.Atoi(choice); err == nil {
		if n < 1 || n > len(c.Apps) {
			return Entry{}, fmt.Errorf("no app numbered %d", n)
		}
		return c.Apps[n-1], nil
	}
	if e, ok := c.Lookup(choice); ok {
		return e, nil
	}
	return Entry{}, fmt.Errorf("unknown app %q", choice)
}
