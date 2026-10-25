package host

import (
	"bytes"
	"errors"
	"strings"
	"testing"

	"github.com/imjasonh/playground/go-plugin/filter"
)

type failFilter struct{}

func (failFilter) Name() string { return "fail" }

func (failFilter) Apply(string) (string, error) {
	return "", errors.New("boom")
}

func TestApplyReturnsInputWhenEmpty(t *testing.T) {
	got, err := Apply(nil, "x")
	if err != nil {
		t.Fatal(err)
	}
	if got != "x" {
		t.Fatalf("Apply() = %q, want x", got)
	}
}

func TestApplyStopsOnError(t *testing.T) {
	_, err := Apply([]filter.Filter{failFilter{}}, "x")
	if err == nil {
		t.Fatal("Apply returned nil error")
	}
	if !strings.Contains(err.Error(), "fail: boom") {
		t.Fatal(err)
	}
}

func TestRunWritesEachLine(t *testing.T) {
	var buf bytes.Buffer
	if err := Run(&buf, nil, strings.NewReader("a\nb\n")); err != nil {
		t.Fatal(err)
	}
	if buf.String() != "a\nb\n" {
		t.Fatalf("Run wrote %q", buf.String())
	}
}

func TestParseFilterArg(t *testing.T) {
	spec, err := parseFilterArg("./redact.so?word=secret&note=a%20b")
	if err != nil {
		t.Fatal(err)
	}
	if spec.path != "./redact.so" {
		t.Fatalf("path = %q", spec.path)
	}
	if spec.cfg["word"] != "secret" || spec.cfg["note"] != "a b" {
		t.Fatalf("config = %#v", spec.cfg)
	}

	spec, err = parseFilterArg("./upper.so")
	if err != nil {
		t.Fatal(err)
	}
	if spec.path != "./upper.so" || len(spec.cfg) != 0 {
		t.Fatalf("spec = %#v", spec)
	}

	if _, err := parseFilterArg("?word=secret"); err == nil {
		t.Fatal("empty path was accepted")
	}
	if _, err := parseFilterArg("p.so?word=a&word=b"); err == nil {
		t.Fatal("repeated key was accepted")
	}
}

func TestRunCLIRequiresFilter(t *testing.T) {
	if err := RunCLI(nil, strings.NewReader(""), &bytes.Buffer{}); err == nil {
		t.Fatal("RunCLI accepted no filters")
	}
}

func TestRunCLIHelp(t *testing.T) {
	var buf bytes.Buffer
	if err := RunCLI([]string{"-h"}, strings.NewReader(""), &buf); err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(buf.String(), "-filter") {
		t.Fatalf("help = %q", buf.String())
	}
}

func TestRunCLIRejectsExtraArgs(t *testing.T) {
	if err := RunCLI([]string{"-filter", "p.so", "extra"}, strings.NewReader(""), &bytes.Buffer{}); err == nil {
		t.Fatal("RunCLI accepted an extra argument")
	}
}
