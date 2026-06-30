package main

import (
	"encoding/csv"
	"encoding/json"
	"fmt"
	"io"
	"strconv"
	"strings"
	"unicode/utf8"
)

// printer renders query results in one of several formats.
type printer struct {
	format   string
	maxWidth int
}

func (p *printer) print(w io.Writer, cols []string, rows [][]any) error {
	switch strings.ToLower(p.format) {
	case "", "table":
		return p.printTable(w, cols, rows)
	case "csv":
		return p.printSeparated(w, cols, rows, ',')
	case "tsv":
		return p.printSeparated(w, cols, rows, '\t')
	case "json":
		return p.printJSON(w, cols, rows)
	case "md", "markdown":
		return p.printMarkdown(w, cols, rows)
	default:
		return fmt.Errorf("unknown format %q (use table, csv, tsv, json, or md)", p.format)
	}
}

func (p *printer) printTable(w io.Writer, cols []string, rows [][]any) error {
	cells := make([][]string, len(rows))
	for i, r := range rows {
		cells[i] = p.formatRow(r)
	}
	widths := make([]int, len(cols))
	for i, c := range cols {
		widths[i] = utf8.RuneCountInString(c)
	}
	for _, r := range cells {
		for i, c := range r {
			if n := utf8.RuneCountInString(c); n > widths[i] {
				widths[i] = n
			}
		}
	}

	printLine := func(parts []string) {
		var b strings.Builder
		for i, s := range parts {
			if i > 0 {
				b.WriteString("  ")
			}
			b.WriteString(s)
			b.WriteString(strings.Repeat(" ", widths[i]-utf8.RuneCountInString(s)))
		}
		fmt.Fprintln(w, strings.TrimRight(b.String(), " "))
	}

	printLine(cols)
	seps := make([]string, len(cols))
	for i, n := range widths {
		seps[i] = strings.Repeat("-", n)
	}
	printLine(seps)
	for _, r := range cells {
		printLine(r)
	}
	if len(rows) == 0 {
		fmt.Fprintln(w, "(0 rows)")
	}
	return nil
}

func (p *printer) printSeparated(w io.Writer, cols []string, rows [][]any, comma rune) error {
	cw := csv.NewWriter(w)
	cw.Comma = comma
	if err := cw.Write(cols); err != nil {
		return err
	}
	for _, r := range rows {
		if err := cw.Write(p.rawRow(r)); err != nil {
			return err
		}
	}
	cw.Flush()
	return cw.Error()
}

func (p *printer) printJSON(w io.Writer, cols []string, rows [][]any) error {
	out := make([]map[string]any, 0, len(rows))
	for _, r := range rows {
		m := make(map[string]any, len(cols))
		for i, c := range cols {
			m[c] = jsonValue(r[i])
		}
		out = append(out, m)
	}
	enc := json.NewEncoder(w)
	enc.SetIndent("", "  ")
	return enc.Encode(out)
}

func (p *printer) printMarkdown(w io.Writer, cols []string, rows [][]any) error {
	esc := func(s string) string { return strings.ReplaceAll(s, "|", "\\|") }
	fmt.Fprintln(w, "| "+strings.Join(mapStr(cols, esc), " | ")+" |")
	seps := make([]string, len(cols))
	for i := range seps {
		seps[i] = "---"
	}
	fmt.Fprintln(w, "| "+strings.Join(seps, " | ")+" |")
	for _, r := range rows {
		fmt.Fprintln(w, "| "+strings.Join(mapStr(p.formatRow(r), esc), " | ")+" |")
	}
	return nil
}

// formatRow renders a row for display, applying width truncation.
func (p *printer) formatRow(r []any) []string {
	out := make([]string, len(r))
	for i, v := range r {
		out[i] = p.truncate(displayValue(v))
	}
	return out
}

// rawRow renders a row without truncation (for csv/tsv).
func (p *printer) rawRow(r []any) []string {
	out := make([]string, len(r))
	for i, v := range r {
		out[i] = displayValue(v)
	}
	return out
}

func (p *printer) truncate(s string) string {
	s = strings.ReplaceAll(s, "\n", " ")
	if p.maxWidth <= 0 || utf8.RuneCountInString(s) <= p.maxWidth {
		return s
	}
	runes := []rune(s)
	if p.maxWidth <= 1 {
		return string(runes[:p.maxWidth])
	}
	return string(runes[:p.maxWidth-1]) + "…"
}

func displayValue(v any) string {
	switch x := v.(type) {
	case nil:
		return ""
	case []byte:
		return string(x)
	case string:
		return x
	case int64:
		return strconv.FormatInt(x, 10)
	case float64:
		return strconv.FormatFloat(x, 'g', -1, 64)
	case bool:
		if x {
			return "1"
		}
		return "0"
	default:
		return fmt.Sprint(x)
	}
}

func jsonValue(v any) any {
	if b, ok := v.([]byte); ok {
		return string(b)
	}
	return v
}

func mapStr(in []string, f func(string) string) []string {
	out := make([]string, len(in))
	for i, s := range in {
		out[i] = f(s)
	}
	return out
}
