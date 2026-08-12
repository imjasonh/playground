// Package e2e shallow-clones real public repos and runs pasta against
// them with a realistic multi-language style-rule set. These are smoke
// tests: they assert the run completes cleanly (no crash, no parse
// hang) and that autofix can rewrite files without error — not golden
// diagnostics.
//
// Languages exercised today: Go, JavaScript, TypeScript, Python, Rust,
// YAML, Java, CSS, PHP (via analyzers + file-extension discovery).
//
// Skip with `go test -short`. CI runs them as part of `go test ./...`.
package e2e_test

import (
	"bytes"
	"context"
	"io/fs"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/imjasonh/pasta/internal/apply"
	"github.com/imjasonh/pasta/internal/dsl"
	"github.com/imjasonh/pasta/internal/lang"
	"github.com/imjasonh/pasta/internal/runner"
)

// fixRules are sparse style/syntax rules that both diagnose and
// rewrite. Kept free of cross-file `requires` so the streaming path
// (and content-sniff pre-filter) stay engaged.
var fixRules = []string{
	// JavaScript / TypeScript
	"js_object_assign_spread",
	"js_double_equals",
	"js_template_no_subst",
	"ts_array_type_style",
	// Go
	"go_negcmp",
	"go_empty_else",
	"go_string_concat_empty",
	"go_self_assignment",
	"go_errors_is_nil",
	// Python
	"python_eq_none",
	"python_bare_except",
	"python_dict_get_redundant_none",
	"python_isinstance_singleton",
	"python_explicit_object_base",
	// Rust
	"rust_needless_bool",
	"rust_println_redundant_format",
	// YAML / CSS / Java / PHP
	"yaml_truthy",
	"css_zero_unit",
	"java_string_equals_literal",
	"php_loose_equality",
}

// diagnoseOnlyRules add signal without rewrites — still useful for
// scan scalability (pre-filter + parse budget).
var diagnoseOnlyRules = []string{
	"ts_any_type",
	"go_panic_empty",
	"js_empty_promise",
	"js_array_concat_spread",
	"js_var_to_let", // report-only — scope-unsafe to autofix
	"python_mutable_default",
	"rust_dbg_macro",
	"rust_println_panic",
	"yaml_empty_value",
	"html_deprecated_tags",
	"html_img_alt",
	"css_important",
	"java_system_out_println",
	"java_finalizer",
	"php_debug_output",
}

type smokeRepo struct {
	name string
	url  string
	// langs is documentation for humans / test logs — which languages
	// this clone is expected to exercise.
	langs []string
	// autofix runs a second pass that applies rewrite ops and writes
	// changed files back to disk, then re-scans.
	autofix bool
	// softExpectFix logs (does not fail) when autofix rewrote zero
	// files. Upstream trees can go clean under our rules without that
	// meaning pasta broke — keep the signal without flaking CI.
	softExpectFix bool
}

// smokeRepos mixes small sanity checks with larger, more complex
// trees so cold-run streaming / pre-filter / parse-budget behaviour
// gets real exercise. All clones are --depth=1.
var smokeRepos = []smokeRepo{
	// --- small sanity (fast) ---
	{
		name:  "golang-example",
		url:   "https://github.com/golang/example",
		langs: []string{"go"},
	},
	{
		name:  "debug-js",
		url:   "https://github.com/debug-js/debug",
		langs: []string{"js"},
	},
	{
		name:  "sindresorhus-is",
		url:   "https://github.com/sindresorhus/is",
		langs: []string{"ts"},
	},

	// --- larger / more complex scan targets ---
	{
		name:    "spf13-cobra",
		url:     "https://github.com/spf13/cobra",
		langs:   []string{"go"},
		autofix: true,
	},
	{
		name:    "gin-gonic-gin",
		url:     "https://github.com/gin-gonic/gin",
		langs:   []string{"go"},
		autofix: true,
	},
	{
		name:    "stretchr-testify",
		url:     "https://github.com/stretchr/testify",
		langs:   []string{"go"},
		autofix: true,
	},
	{
		name:          "expressjs-express",
		url:           "https://github.com/expressjs/express",
		langs:         []string{"js"},
		autofix:       true,
		softExpectFix: true,
	},
	{
		name:          "axios-axios",
		url:           "https://github.com/axios/axios",
		langs:         []string{"js", "ts"},
		autofix:       true,
		softExpectFix: true,
	},
	{
		name:          "jashkenas-underscore",
		url:           "https://github.com/jashkenas/underscore",
		langs:         []string{"js"},
		autofix:       true,
		softExpectFix: true,
	},
	{
		name:          "colinhacks-zod",
		url:           "https://github.com/colinhacks/zod",
		langs:         []string{"ts"},
		autofix:       true,
		softExpectFix: true,
	},
	{
		name:          "pallets-flask",
		url:           "https://github.com/pallets/flask",
		langs:         []string{"python"},
		autofix:       true,
		softExpectFix: true,
	},
	{
		name:          "psf-requests",
		url:           "https://github.com/psf/requests",
		langs:         []string{"python"},
		autofix:       true,
		softExpectFix: true,
	},
	{
		name:    "encode-httpx",
		url:     "https://github.com/encode/httpx",
		langs:   []string{"python"},
		autofix: true,
	},
	{
		name:    "clap-rs-clap",
		url:     "https://github.com/clap-rs/clap",
		langs:   []string{"rust"},
		autofix: true,
	},
	{
		name:    "serde-rs-json",
		url:     "https://github.com/serde-rs/json",
		langs:   []string{"rust"},
		autofix: true,
	},
	{
		name:    "BurntSushi-toml",
		url:     "https://github.com/BurntSushi/toml",
		langs:   []string{"rust"},
		autofix: true,
	},
	{
		name:    "square-okhttp",
		url:     "https://github.com/square/okhttp",
		langs:   []string{"java"},
		autofix: true,
	},
	{
		name:          "nikic-PHP-Parser",
		url:           "https://github.com/nikic/PHP-Parser",
		langs:         []string{"php"},
		autofix:       true,
		softExpectFix: true,
	},
	{
		name:          "twbs-bootstrap",
		url:           "https://github.com/twbs/bootstrap",
		langs:         []string{"js", "css", "html"},
		autofix:       true,
		softExpectFix: true,
	},
	// YAML-heavy workflow / config trees.
	{
		name:    "actions-starter-workflows",
		url:     "https://github.com/actions/starter-workflows",
		langs:   []string{"yaml"},
		autofix: true,
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
	analyzers := loadRules(t, repoRoot, append(append([]string{}, fixRules...), diagnoseOnlyRules...))

	for _, repo := range smokeRepos {
		repo := repo
		t.Run(repo.name, func(t *testing.T) {
			if parallelSmoke {
				t.Parallel()
			}
			dir := shallowClone(t, repo.url)
			specs := collectSpecs(t, dir, repo)
			if len(specs) == 0 {
				t.Fatalf("no source files discovered under %s (langs=%v)", dir, repo.langs)
			}
			t.Logf("scanning %d files from %s (langs=%v)", len(specs), repo.url, repo.langs)

			ctx, cancel := context.WithTimeout(t.Context(), 8*time.Minute)
			defer cancel()

			start := time.Now()
			results, err := runner.RunGroup(ctx, specs, analyzers, false,
				runner.WithParseTimeout(2*time.Second),
			)
			elapsed := time.Since(start)
			if err != nil {
				t.Fatalf("RunGroup (scan): %v", err)
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
			t.Logf("scan ok in %s: %d files, %d diagnostics, %d parse-budget skips",
				elapsed.Round(time.Millisecond), len(specs), diags, skipped)

			if !repo.autofix {
				return
			}
			runAutofix(t, ctx, dir, specs, analyzers, repo.softExpectFix)
		})
	}
}

func runAutofix(t *testing.T, ctx context.Context, dir string, specs []runner.FileSpec, analyzers []*dsl.Analyzer, softExpectFix bool) {
	t.Helper()
	// Apply per-file so one overlapping-edit conflict (common with
	// nested `var` rewrites on older JS) doesn't abort the whole tree.
	start := time.Now()
	results, err := runner.RunGroup(ctx, specs, analyzers, false,
		runner.WithParseTimeout(2*time.Second),
	)
	if err != nil {
		t.Fatalf("RunGroup (autofix scan): %v", err)
	}
	var changed, skipped, conflicts int
	for _, r := range results {
		if r.SkipReason != "" {
			skipped++
			continue
		}
		if len(r.Ops) == 0 {
			continue
		}
		orig, err := os.ReadFile(r.Path)
		if err != nil {
			t.Fatalf("read %s: %v", r.Path, err)
		}
		fixed, err := apply.Apply(orig, r.Ops, dsl.RewriteOpts{})
		if err != nil {
			// Conflicting overlapping edits are expected on dense legacy
			// JS; log and continue so the smoke still covers the rest.
			if strings.Contains(err.Error(), "conflicting edits") {
				conflicts++
				t.Logf("autofix conflict %s: %v", r.Path, err)
				continue
			}
			t.Fatalf("apply %s: %v", r.Path, err)
		}
		if bytes.Equal(orig, fixed) {
			continue
		}
		if err := os.WriteFile(r.Path, fixed, 0o644); err != nil {
			t.Fatalf("write %s: %v", r.Path, err)
		}
		changed++
	}
	t.Logf("autofix ok in %s under %s: %d files rewritten, %d conflicts, %d skipped",
		time.Since(start).Round(time.Millisecond), dir, changed, conflicts, skipped)

	if softExpectFix && changed == 0 {
		t.Logf("note: expected rewrites in %s but none landed (conflicts=%d); upstream may be clean", dir, conflicts)
	}

	// Second pass over the rewritten tree must still succeed (no crash).
	results2, err := runner.RunGroup(ctx, specs, analyzers, false,
		runner.WithParseTimeout(2*time.Second),
	)
	if err != nil {
		t.Fatalf("RunGroup (post-fix scan): %v", err)
	}
	if len(results2) != len(specs) {
		t.Fatalf("post-fix: got %d results, want %d", len(results2), len(specs))
	}
}

func loadRules(t *testing.T, repoRoot string, names []string) []*dsl.Analyzer {
	t.Helper()
	var out []*dsl.Analyzer
	for _, name := range names {
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
	var lastOut []byte
	var lastErr error
	for attempt := 1; attempt <= 3; attempt++ {
		ctx, cancel := context.WithTimeout(t.Context(), 3*time.Minute)
		cmd := exec.CommandContext(ctx, "git", "clone", "--depth=1", "--quiet", url, dir)
		cmd.Env = append(os.Environ(), "GIT_TERMINAL_PROMPT=0")
		lastOut, lastErr = cmd.CombinedOutput()
		cancel()
		if lastErr == nil {
			return dir
		}
		// Wipe partial clone contents before retry.
		_ = os.RemoveAll(dir)
		if err := os.MkdirAll(dir, 0o755); err != nil {
			t.Fatalf("mkdir %s: %v", dir, err)
		}
		t.Logf("git clone %s attempt %d failed: %v", url, attempt, lastErr)
		time.Sleep(time.Duration(attempt) * time.Second)
	}
	// Network flakes shouldn't fail the whole suite hard — skip.
	t.Skipf("git clone %s failed after retries: %v\n%s", url, lastErr, lastOut)
	return dir
}

// collectSpecs walks the clone the same way the CLI's ./... expansion
// does: any extension pasta knows about, skipping VCS / vendor trees.
// php-src is capped to Zend/ + ext/standard/ so the smoke stays bounded.
func collectSpecs(t *testing.T, root string, repo smokeRepo) []runner.FileSpec {
	t.Helper()
	skip := map[string]bool{}
	for k := range runner.DefaultSkipDirs {
		skip[k] = true
	}
	// Smoke-only extras: keep clones bounded (build outputs / fixtures).
	for _, k := range []string{"target", "dist", "build", "testdata"} {
		skip[k] = true
	}
	var specs []runner.FileSpec
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
		name := d.Name()
		if runner.IsGeneratedLockfile(name) {
			return nil
		}
		if _, ok := lang.ByExt(filepath.Ext(name)); !ok {
			return nil
		}
		info, ierr := d.Info()
		if ierr == nil && info.Size() > 1<<20 {
			return nil
		}
		specs = append(specs, runner.FileSpec{Path: p})
		return nil
	})
	if err != nil {
		t.Fatalf("walk %s: %v", root, err)
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
