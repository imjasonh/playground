package loader

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"

	"cuelang.org/go/cue"
	"cuelang.org/go/cue/cuecontext"

	"github.com/imjasonh/pasta/internal/dsl"
	"github.com/imjasonh/pasta/internal/remote"
)

// Config is project-level configuration loaded from the rule
// directory's `pasta.cue` (the same file that holds the remote-imports
// manifest). Every field is optional; an absent file is equivalent to
// an empty Config.
//
//	imports: { "github.com/alice/lint-rules": "v1.2.3" } // remote rules
//	disabled_rules: ["go_iferr", "todo_format"]          // skip analyzers or rules
//	severity:       {go_panic_empty: "error"}            // override per analyzer/rule
//	skip:           ["build", "dist"]                    // extra ./... walk skip-dirs
//	max_file_size:  2_000_000                            // bytes; 0 = unlimited
//	parse_timeout_ms: 2000                               // per-file parse budget in ms; 0 = unlimited
//	memory_budget:  512_000_000                          // cumulative parsed source bytes; 0 = unlimited
//
// `imports` is consumed by internal/remote (LoadManifest); this loader
// only reads the config-relevant fields. Co-locating them in one file
// keeps a project's pasta-side metadata in a single place.
type Config struct {
	DisabledRules []string          `json:"disabled_rules,omitempty"`
	Severity      map[string]string `json:"severity,omitempty"`
	Skip          []string          `json:"skip,omitempty"`

	// MaxFileSize is the size cap, in bytes, applied during `./...`
	// expansion: files larger than this are dropped from the source
	// list. Nil means "not specified" — the CLI applies its own
	// default (1 MiB). A pointer to 0 means "no cap; analyze
	// everything"; users opting into unlimited mode set this
	// explicitly to override the default.
	MaxFileSize *int64 `json:"max_file_size,omitempty"`

	// ParseTimeout is the per-file tree-sitter parse budget. Nil means
	// "not specified" — the engine applies its default (2s). A pointer
	// to 0 disables the budget. Negative values are rejected at load.
	ParseTimeout *int64 `json:"parse_timeout_ms,omitempty"`

	// MemoryBudget is a cumulative cap on source bytes admitted to
	// parse in one run. Nil means "not specified" (unlimited). A
	// pointer to 0 also means unlimited. When exceeded, further files
	// are skipped (like parse timeout) — the run does not fail.
	MemoryBudget *int64 `json:"memory_budget,omitempty"`
}

// LoadConfig reads `<dir>/pasta.cue` and extracts the config-relevant
// fields. Returns (nil, false, nil) when the file doesn't exist;
// callers treat that as "no project config". A file that exists but
// declares only `imports` (no config fields) yields an empty Config
// with ok=true. Validation errors (bad CUE, unknown severity value)
// come back as a non-nil error.
func LoadConfig(dir string) (*Config, bool, error) {
	path := filepath.Join(dir, remote.ManifestFile)
	src, err := os.ReadFile(path)
	if os.IsNotExist(err) {
		return nil, false, nil
	}
	if err != nil {
		return nil, false, fmt.Errorf("read %s: %w", path, err)
	}
	ctx := cuecontext.New()
	v := ctx.CompileBytes(src, cue.Filename(path))
	if err := v.Err(); err != nil {
		return nil, false, fmt.Errorf("parse %s: %s", path, cueErrDetails(err))
	}
	cfg := &Config{}
	if err := decodeStringList(v, "disabled_rules", &cfg.DisabledRules); err != nil {
		return nil, false, fmt.Errorf("%s: %w", path, err)
	}
	if err := decodeStringList(v, "skip", &cfg.Skip); err != nil {
		return nil, false, fmt.Errorf("%s: %w", path, err)
	}
	if mfs := v.LookupPath(cue.ParsePath("max_file_size")); mfs.Exists() {
		n, err := mfs.Int64()
		if err != nil {
			return nil, false, fmt.Errorf("%s: max_file_size must be an integer: %w", path, err)
		}
		if n < 0 {
			return nil, false, fmt.Errorf("%s: max_file_size must be >= 0 (got %d)", path, n)
		}
		cfg.MaxFileSize = &n
	}
	if pt := v.LookupPath(cue.ParsePath("parse_timeout_ms")); pt.Exists() {
		n, err := pt.Int64()
		if err != nil {
			return nil, false, fmt.Errorf("%s: parse_timeout_ms must be an integer: %w", path, err)
		}
		if n < 0 {
			return nil, false, fmt.Errorf("%s: parse_timeout_ms must be >= 0 (got %d)", path, n)
		}
		cfg.ParseTimeout = &n
	}
	if mb := v.LookupPath(cue.ParsePath("memory_budget")); mb.Exists() {
		n, err := mb.Int64()
		if err != nil {
			return nil, false, fmt.Errorf("%s: memory_budget must be an integer: %w", path, err)
		}
		if n < 0 {
			return nil, false, fmt.Errorf("%s: memory_budget must be >= 0 (got %d)", path, n)
		}
		cfg.MemoryBudget = &n
	}
	sev := v.LookupPath(cue.ParsePath("severity"))
	if sev.Exists() {
		jb, err := sev.MarshalJSON()
		if err != nil {
			return nil, false, fmt.Errorf("%s: severity: %w", path, err)
		}
		if err := json.Unmarshal(jb, &cfg.Severity); err != nil {
			return nil, false, fmt.Errorf("%s: severity must be a string→string map: %w", path, err)
		}
		for rule, sev := range cfg.Severity {
			if !validSeverity(sev) {
				return nil, false, fmt.Errorf("%s: severity[%q]: %q is not a valid severity (error|warning|info|hint)", path, rule, sev)
			}
		}
	}
	return cfg, true, nil
}

func decodeStringList(v cue.Value, field string, dst *[]string) error {
	x := v.LookupPath(cue.ParsePath(field))
	if !x.Exists() {
		return nil
	}
	jb, err := x.MarshalJSON()
	if err != nil {
		return fmt.Errorf("%s: %w", field, err)
	}
	if err := json.Unmarshal(jb, dst); err != nil {
		return fmt.Errorf("%s must be a list of strings: %w", field, err)
	}
	return nil
}

func validSeverity(s string) bool {
	switch dsl.Severity(s) {
	case dsl.SeverityError, dsl.SeverityWarning, dsl.SeverityInfo, dsl.SeverityHint:
		return true
	}
	return false
}

// applyConfig mutates analyzers in place: drops rules listed in
// DisabledRules and overrides Diagnose.Severity for rules listed in
// Severity. Returns zero or more human-readable warnings for
// configuration that didn't take effect:
//
//   - a name in DisabledRules that doesn't match any loaded rule
//     or analyzer (typo, or rule was removed upstream),
//   - a key in Severity that doesn't match any loaded rule or
//     analyzer,
//   - a key in Severity whose target rule has no `diagnose` block —
//     overriding severity on a rewrite-only rule is meaningless and
//     would otherwise cause the engine to emit empty-message
//     diagnostics on every match.
//
// Names may refer to either a rule (`eq`, `force_unwrap`) or an
// entire analyzer (`js_double_equals`, `go_iferr`). Analyzer-level
// disable drops every rule in that analyzer; analyzer-level severity
// rewrites every diagnose-bearing rule it contains.
//
// Callers (LoadDir) print these warnings to stderr. Both maps being
// empty is a no-op, so callers can pass a possibly-nil Config.
//
// Rule identity is `rule.Name` — the loader (`tryDecodeAnalyzer`)
// guarantees Name is set, defaulting to the map key when absent, so
// matching against Name covers both authoring conventions.
func applyConfig(cfg *Config, analyzers []*dsl.Analyzer) []string {
	if cfg == nil {
		return nil
	}
	// Index every rule across every analyzer first. Two passes over
	// the rules — one to build the index, one to mutate — so the
	// typo warnings don't fire against rules we just removed, and
	// so each severity-override decision is an O(1) lookup instead
	// of an O(rules) scan.
	knownRule := map[string]bool{}
	knownAnalyzer := map[string]bool{}
	withDiagnose := map[string]bool{}
	analyzerHasDiagnose := map[string]bool{}
	for _, a := range analyzers {
		knownAnalyzer[a.Name] = true
		for _, rule := range a.Rules {
			knownRule[rule.Name] = true
			if rule.Diagnose != nil {
				withDiagnose[rule.Name] = true
				analyzerHasDiagnose[a.Name] = true
			}
		}
	}

	var warns []string
	disabled := map[string]bool{}
	for _, r := range cfg.DisabledRules {
		disabled[r] = true
		if !knownRule[r] && !knownAnalyzer[r] {
			warns = append(warns, fmt.Sprintf("disabled_rules: %q is not a loaded rule or analyzer", r))
		}
	}
	for r, sev := range cfg.Severity {
		if !knownRule[r] && !knownAnalyzer[r] {
			warns = append(warns, fmt.Sprintf("severity: %q is not a loaded rule or analyzer", r))
			continue
		}
		if disabled[r] {
			// User asked to disable it AND override its severity.
			// The disable wins; surfacing both as no-ops would just
			// be noise.
			continue
		}
		if knownRule[r] && !withDiagnose[r] {
			warns = append(warns, fmt.Sprintf("severity: rule %q has no diagnose block; severity %q would not take effect", r, sev))
			continue
		}
		if knownAnalyzer[r] && !knownRule[r] && !analyzerHasDiagnose[r] {
			warns = append(warns, fmt.Sprintf("severity: analyzer %q has no diagnose-bearing rules; severity %q would not take effect", r, sev))
		}
	}

	for _, a := range analyzers {
		if disabled[a.Name] {
			a.Rules = map[string]dsl.Rule{}
			continue
		}
		analyzerSev, hasAnalyzerSev := cfg.Severity[a.Name]
		for name, rule := range a.Rules {
			if disabled[rule.Name] {
				delete(a.Rules, name)
				continue
			}
			sev, ok := cfg.Severity[rule.Name]
			if !ok {
				sev, ok = analyzerSev, hasAnalyzerSev
			}
			if !ok || rule.Diagnose == nil {
				continue
			}
			rule.Diagnose.Severity = dsl.Severity(sev)
			a.Rules[name] = rule
		}
	}
	return warns
}
