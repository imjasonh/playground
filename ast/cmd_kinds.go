package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"strings"

	"github.com/imjasonh/playground/ast/internal/langs"
	"github.com/imjasonh/playground/ast/internal/nav"
)

func cmdKinds(args []string, stdout io.Writer) error {
	fs := flag.NewFlagSet("kinds", flag.ContinueOnError)
	fs.SetOutput(stdout)
	var langName string
	fs.StringVar(&langName, "l", "", "show which kinds are available for this language")
	fs.StringVar(&langName, "lang", "", "show which kinds are available for this language")
	asJSON := fs.Bool("json", false, "output as JSON")
	if err := fs.Parse(args); err != nil {
		return err
	}

	if langName != "" {
		l, ok := langs.ByName(langName)
		if !ok {
			return fmt.Errorf("unknown language %q (see `%s languages`)", langName, progName)
		}
		available := nav.KindsForLanguage(l)
		if *asJSON {
			enc := json.NewEncoder(stdout)
			enc.SetIndent("", "  ")
			return enc.Encode(map[string]any{"language": l.Name, "kinds": available})
		}
		if len(available) == 0 {
			fmt.Fprintf(stdout, "no --kind selectors available for %s (use -q with a tree-sitter query)\n", l.Name)
			return nil
		}
		fmt.Fprintf(stdout, "kinds available for %s:\n  %s\n", l.Name, strings.Join(available, " "))
		return nil
	}

	all := nav.AllKinds()
	if *asJSON {
		enc := json.NewEncoder(stdout)
		enc.SetIndent("", "  ")
		return enc.Encode(all)
	}
	fmt.Fprintf(stdout, "normalized kinds (use with `ast query --kind`):\n  %s\n", strings.Join(all, " "))
	fmt.Fprintln(stdout, "\nRun `ast kinds -l <language>` to see which are available for a language.")
	return nil
}
