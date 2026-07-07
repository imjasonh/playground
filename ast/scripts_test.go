package main

import (
	"flag"
	"os"
	"testing"

	"github.com/rogpeppe/go-internal/testscript"
)

// update regenerates the golden output embedded in the testscript files:
//
//	go test ./... -run TestScripts -update
var update = flag.Bool("update", false, "update testscript golden files")

// TestMain registers the ast CLI as a command usable inside testscript files.
// Scripts invoke it as "ast ...", exactly as a user would on the command line.
func TestMain(m *testing.M) {
	os.Exit(testscript.RunMain(m, map[string]func() int{
		"ast": astMain,
	}))
}

// TestScripts runs the golden CLI tests under testdata/scripts. Each *.txtar
// file embeds source files in various languages, runs ast against them, and
// asserts the output matches embedded golden files with `cmp`. Regenerate the
// golden output with `go test -run TestScripts -update`.
func TestScripts(t *testing.T) {
	testscript.Run(t, testscript.Params{
		Dir:           "testdata/scripts",
		UpdateScripts: *update,
	})
}
