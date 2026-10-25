package host

import (
	"errors"
	"flag"
	"fmt"
	"io"
	"net/url"
	"strings"

	"github.com/imjasonh/playground/go-plugin/filter"
)

type filterSpec struct {
	path string
	cfg  filter.Config
}

type filtersFlag []filterSpec

func (f *filtersFlag) String() string {
	if f == nil || len(*f) == 0 {
		return ""
	}
	parts := make([]string, len(*f))
	for i, spec := range *f {
		parts[i] = spec.path
	}
	return strings.Join(parts, ",")
}

func (f *filtersFlag) Set(s string) error {
	spec, err := parseFilterArg(s)
	if err != nil {
		return err
	}
	*f = append(*f, spec)
	return nil
}

func parseFilterArg(s string) (filterSpec, error) {
	path, raw, ok := strings.Cut(s, "?")
	if path == "" {
		return filterSpec{}, errors.New("empty plugin path")
	}
	cfg := filter.Config{}
	if !ok {
		return filterSpec{path: path, cfg: cfg}, nil
	}
	q, err := url.ParseQuery(raw)
	if err != nil {
		return filterSpec{}, fmt.Errorf("parse config: %w", err)
	}
	for k, vs := range q {
		if k == "" {
			return filterSpec{}, errors.New("empty config key")
		}
		if len(vs) != 1 {
			return filterSpec{}, fmt.Errorf("config key %s has %d values", k, len(vs))
		}
		cfg[k] = vs[0]
	}
	return filterSpec{path: path, cfg: cfg}, nil
}

// RunCLI loads each -filter and writes filtered lines from in to out.
// A filter argument is a plugin path. An optional query string is the
// config passed to NewFilter, as in redact.so?word=secret.
func RunCLI(args []string, in io.Reader, out io.Writer) error {
	var specs filtersFlag
	fs := flag.NewFlagSet("host", flag.ContinueOnError)
	fs.SetOutput(out)
	fs.Var(&specs, "filter", "plugin path, optional ?k=v config for NewFilter; repeat to chain")
	fs.Usage = func() {
		fmt.Fprintf(out, "Usage: host -filter path[?k=v] [-filter ...]\n\n")
		fs.PrintDefaults()
	}
	if err := fs.Parse(args); err != nil {
		if errors.Is(err, flag.ErrHelp) {
			return nil
		}
		return err
	}
	if fs.NArg() != 0 {
		return fmt.Errorf("unexpected arguments: %s", strings.Join(fs.Args(), " "))
	}
	if len(specs) == 0 {
		return errors.New("at least one -filter is required")
	}
	loaded := make([]filter.Filter, 0, len(specs))
	for _, spec := range specs {
		f, err := Load(spec.path, spec.cfg)
		if err != nil {
			return fmt.Errorf("load %s: %w", spec.path, err)
		}
		loaded = append(loaded, f)
	}
	return Run(out, loaded, in)
}
