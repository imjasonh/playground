//go:build !kube_nogenerate

package kube

import (
	"context"
	"flag"
	"fmt"
	"io"
	"maps"
	"slices"
	"strings"

	"github.com/imjasonh/playground/kube/internal/image"
)

// generateImages resolves tags on the developer's machine, with the
// credentials that generate pushes the program's image with.
var generateImages = &imageDigests{digest: image.Digest}

// pinImageFlags resolves the tags in the program's image flags, and sets
// those flags to the images by digest in the Deployment's arguments.
func (o *generateOptions) pinImageFlags(ctx context.Context) error {
	pinned, err := generateImages.pinFlags(ctx, flag.CommandLine, func(name, from, to string) {
		o.logf("resolved -%s=%s to %s", name, from, to)
	})
	if err != nil {
		return fmt.Errorf("generate: %w", err)
	}
	if len(pinned) > 0 {
		o.args = setFlags(o.args, o.programFlags(), pinned)
	}
	return nil
}

// pinImages resolves the tags of the images in the containers of docs.
func (o *generateOptions) pinImages(ctx context.Context, docs []object) error {
	for _, d := range docs {
		if err := generateImages.pinImages(ctx, d, func(from, to string) {
			o.logf("resolved %s to %s", from, to)
		}); err != nil {
			meta, _ := d.get("metadata").(object)
			return fmt.Errorf("generate: %v %v: %w", d.get("kind"), meta.get("name"), err)
		}
	}
	return nil
}

// programFlags returns the flags of the program in the Deployment: its own,
// and Main's, as parseProgramFlags parses them.
func (o *generateOptions) programFlags() *flag.FlagSet {
	fs := flag.NewFlagSet("", flag.ContinueOnError)
	fs.SetOutput(io.Discard)
	flag.CommandLine.VisitAll(func(f *flag.Flag) { fs.Var(f.Value, f.Name, f.Usage) })
	(&Manager{Logger: o.manager.Logger}).flags(fs)
	return fs
}

// setFlags returns args, the arguments of a program with the flags fs, with
// each flag in values set to its value. It replaces the flag where args set
// it, and adds it after the flags in args where they don't.
func setFlags(args []string, fs *flag.FlagSet, values map[string]string) []string {
	out := make([]string, 0, len(args)+len(values))
	set := map[string]bool{}
	i := 0
	for i < len(args) {
		s := args[i]
		if len(s) < 2 || s[0] != '-' || s == "--" {
			break
		}
		dashes := "-"
		if s[1] == '-' {
			dashes = "--"
		}
		name, _, hasValue := strings.Cut(s[len(dashes):], "=")
		i++
		// As in the flag package, a flag without "=" takes the next
		// argument as its value, unless it's a bool flag.
		separate := !hasValue && i < len(args) && !isBoolFlag(fs.Lookup(name))
		if v, ok := values[name]; ok {
			out = append(out, dashes+name+"="+v)
			set[name] = true
		} else {
			out = append(out, s)
			if separate {
				out = append(out, args[i])
			}
		}
		if separate {
			i++
		}
	}
	for _, name := range slices.Sorted(maps.Keys(values)) {
		if !set[name] {
			out = append(out, "-"+name+"="+values[name])
		}
	}
	return append(out, args[i:]...)
}

func isBoolFlag(f *flag.Flag) bool {
	if f == nil {
		return false
	}
	b, ok := f.Value.(interface{ IsBoolFlag() bool })
	return ok && b.IsBoolFlag()
}

func (o object) get(key string) any {
	for _, f := range o {
		if f.key == key {
			return f.value
		}
	}
	return nil
}

// set sets the value of key, if o has key.
func (o object) set(key string, value any) {
	for i := range o {
		if o[i].key == key {
			o[i].value = value
		}
	}
}
