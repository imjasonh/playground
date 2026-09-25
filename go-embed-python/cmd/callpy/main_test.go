package main

import (
	"bytes"
	"strings"
	"testing"
)

func TestRun(t *testing.T) {
	var out bytes.Buffer
	if err := run(&out); err != nil {
		t.Fatalf("run: %v\n%s", err, out.String())
	}
	for _, want := range []string{
		"[Go, called from Python] summarize() received 4 words",
		`count=4 longest="Py_BytesMain"`,
		"same process: true",
		"__file__ = <go:embed wordstats.py>",
		"err = ValueError: bad input from Go",
		"0 wrong results",
	} {
		if !strings.Contains(out.String(), want) {
			t.Errorf("output is missing %q:\n%s", want, out.String())
		}
	}
}
