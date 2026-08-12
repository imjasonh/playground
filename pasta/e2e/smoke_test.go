// Package e2e shallow-clones a few real public repos and runs pasta
// against them with a realistic sparse style-rule set. These are smoke
// tests: they assert the run completes cleanly (no crash, no parse
// hang) rather than golden diagnostics.
//
// Skip with `go test -short`. CI runs them as part of `go test ./...`.
package e2e_test

import (
	"context"
	"io/fs"
	"os"
	"os/exec"
	"path/filepath"
	"testing"
	"time"

	"github.com/imjasonh/pasta/internal/dsl"
	"github.com/imjasonh/pasta/internal/runner"
)

// styleRules are sparse style/syntax rules that benefit from the
// content-sniff pre-filter. They exercise JS/TS/Go without depending
// on cross-file fact passing (so the streaming path is used).
var styleRules = []string{
	"js_var_to_let",
	"js_object_assign_spread",
	"js_double_equals",
	"js_array_concat_spread",
	"ts_array_type_style",
	"ts_any_type",
	"go_negcmp",
	"go_empty_else",
	"go_string_concat_empty",
	"go_panic_empty",
}

type smokeRepo struct {
	name string
	url  string
	// globs passed to pasta as sources after clone (relative to clone root).
	sources []string
}

var smokeRepos = []smokeRepo{
	{
		name:    "golang-example",
		url:     "https://github.com/golang/example",
		sources: []string{"./..."},
	},
	{
		name:    "debug-js",
		url:     "https://github.com/debug-js/debug",
		sources: []string{"./..."},
	},
	{
		name:    "sindresorhus-is",
		url:     "https://github.com/sindresorhus/is",
		sources: []string{"./..."},
	},
	// Medium / representative trees — enough files that the streaming
	// path, content-sniff pre-filter, and parse budget matter.
	{
		name:    "spf13-cobra",
		url:     "https://github.com/spf13/cobra",
		sources: []string{"./..."},
	},
	{
		name:    "expressjs-express",
		url:     "https://github.com/expressjs/express",
		sources: []string{"./..."},
	},
	{
		name:    "chalk-chalk",
		url:     "https://github.com/chalk/chalk",
		sources: []string{"./..."},
	},
}

func TestSmokeRealRepos(t *testing.T) {
	if testing.Short() {
		t.Skip("skipping e2e smoke tests in -short mode")
	}
	if _, err := exec.LookPath("git"); err != nil {
		t.Skip("git not available")
	}

	repoRoot := findPastaRoot(t)
	analyzers := loadStyleRules(t, repoRoot)

	for _, repo := range smokeRepos {
		repo := repo
		t.Run(repo.name, func(t *testing.T) {
			t.Parallel()
			dir := shallowClone(t, repo.url)
			specs := collectSpecs(t, dir, repo.sources)
			if len(specs) == 0 {
				t.Fatalf("no source files discovered under %s", dir)
			}
			t.Logf("scanning %d files from %s", len(specs), repo.url)

			ctx, cancel := context.WithTimeout(t.Context(), 5*time.Minute)
			defer cancel()

			start := time.Now()
			results, err := runner.RunGroup(ctx, specs, analyzers, false,
				runner.WithParseTimeout(2*time.Second),
			)
			elapsed := time.Since(start)
			if err != nil {
				t.Fatalf("RunGroup: %v", err)
			}
			if len(results) != len(specs) {
				t.Fatalf("got %d results, want %d", len(results), len(specs))
			}

			var diags, skipped int
			for _, r := range results {
				if r.SkipReason != "" {
					skipped++
					t.Logf("skip %s: %s", r.Path, r.SkipReason)
					continue
				}
				diags += len(r.Diagnostics)
			}
			t.Logf("ok in %s: %d files, %d diagnostics, %d parse-budget skips",
				elapsed.Round(time.Millisecond), len(specs), diags, skipped)
		})
	}
}

func loadStyleRules(t *testing.T, repoRoot string) []*dsl.Analyzer {
	t.Helper()
	var out []*dsl.Analyzer
	for _, name := range styleRules {
		dir := filepath.Join(repoRoot, "analyzers", name)
		as, err := runner.LoadRules(dir)
		if err != nil {
			t.Fatalf("LoadRules(%s): %v", name, err)
		}
		out = append(out, as...)
	}
	if len(out) == 0 {
		t.Fatal("no analyzers loaded")
	}
	return out
}

func shallowClone(t *testing.T, url string) string {
	t.Helper()
	dir := t.TempDir()
	ctx, cancel := context.WithTimeout(t.Context(), 2*time.Minute)
	defer cancel()
	cmd := exec.CommandContext(ctx, "git", "clone", "--depth=1", "--quiet", url, dir)
	cmd.Env = append(os.Environ(), "GIT_TERMINAL_PROMPT=0")
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("git clone %s: %v\n%s", url, err, out)
	}
	return dir
}

// collectSpecs walks the clone the same way the CLI's ./... expansion
// does: registered extensions only, skipping .git/vendor/node_modules.
func collectSpecs(t *testing.T, root string, sources []string) []runner.FileSpec {
	t.Helper()
	skip := map[string]bool{
		".git": true, "vendor": true, "node_modules": true, ".pasta": true,
	}
	var specs []runner.FileSpec
	for _, src := range sources {
		if src == "./..." || src == "..." || filepath.Base(src) == "..." {
			err := filepath.WalkDir(root, func(p string, d fs.DirEntry, err error) error {
				if err != nil {
					return err
				}
				if d.IsDir() {
					if p != root && skip[d.Name()] {
						return filepath.SkipDir
					}
					return nil
				}
				ext := filepath.Ext(d.Name())
				switch ext {
				case ".go", ".js", ".jsx", ".mjs", ".cjs", ".ts", ".tsx", ".cts", ".mts":
					// Cap like the CLI default so a vendored blob can't
					// dominate the smoke run even if skip missed it.
					info, ierr := d.Info()
					if ierr == nil && info.Size() > 1<<20 {
						return nil
					}
					specs = append(specs, runner.FileSpec{Path: p})
				}
				return nil
			})
			if err != nil {
				t.Fatalf("walk %s: %v", root, err)
			}
			continue
		}
		specs = append(specs, runner.FileSpec{Path: filepath.Join(root, src)})
	}
	return specs
}

// findPastaRoot locates the pasta module root (directory containing
// go.mod + analyzers/). Works whether the test binary's cwd is pasta/
// or pasta/e2e/.
func findPastaRoot(t *testing.T) string {
	t.Helper()
	wd, err := os.Getwd()
	if err != nil {
		t.Fatal(err)
	}
	dir := wd
	for {
		if _, err := os.Stat(filepath.Join(dir, "go.mod")); err == nil {
			if _, err := os.Stat(filepath.Join(dir, "analyzers")); err == nil {
				return dir
			}
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			t.Fatalf("pasta root not found from %s", wd)
		}
		dir = parent
	}
}
