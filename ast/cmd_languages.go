package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"strings"
	"text/tabwriter"

	"github.com/imjasonh/playground/ast/internal/langs"
)

func cmdLanguages(args []string, stdout io.Writer) error {
	fs := flag.NewFlagSet("languages", flag.ContinueOnError)
	fs.SetOutput(stdout)
	asJSON := fs.Bool("json", false, "output as JSON")
	if err := fs.Parse(args); err != nil {
		return err
	}

	all := langs.All()
	if *asJSON {
		type entry struct {
			Name       string   `json:"name"`
			Aliases    []string `json:"aliases"`
			Extensions []string `json:"extensions"`
		}
		out := make([]entry, 0, len(all))
		for _, l := range all {
			out = append(out, entry{Name: l.Name, Aliases: l.Aliases(), Extensions: l.Extensions})
		}
		enc := json.NewEncoder(stdout)
		enc.SetIndent("", "  ")
		return enc.Encode(out)
	}

	tw := tabwriter.NewWriter(stdout, 0, 0, 2, ' ', 0)
	fmt.Fprintln(tw, "LANGUAGE\tALIASES\tEXTENSIONS")
	for _, l := range all {
		aliases := strings.Join(l.Aliases(), " ")
		if aliases == "" {
			aliases = "-"
		}
		fmt.Fprintf(tw, "%s\t%s\t%s\n", l.Name, aliases, strings.Join(l.Extensions, " "))
	}
	if err := tw.Flush(); err != nil {
		return err
	}
	fmt.Fprintf(stdout, "\n%d languages supported\n", len(all))
	return nil
}
