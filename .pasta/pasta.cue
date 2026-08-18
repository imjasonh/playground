// Playground monorepo pasta project config.
// Rules are enrolled as subdirectories of .pasta/ (symlinks into pasta/analyzers/).

package pasta_project

// Analyzer-level disables for rules that are too noisy (or not yet
// actionable) across this multi-app tree. Prefer pasta:ignore for
// one-off lines over growing this list.
disabled_rules: [
	// Scope-unsafe to autofix; still useful locally but floods CI.
	"js_var_to_let",
	// Expect/unwrap is idiomatic in Rust tests and several Workers.
	"rust_unwrap",
	// Many sample/demo apps intentionally use console.log.
	"js_console_log",
	// Games and demos rely on !important for layered UI states.
	"css_important",
	// GitHub Actions uses empty `on:` / `push:` keys idiomatically.
	"yaml_empty_value",
	// XcodeGen project.yml uses YES/NO; canonical true/false breaks tooling.
	"yaml_truthy",
]

// Extra ./... skip dirs on top of pasta defaults (vendor, node_modules,
// testdata, target, …).
skip: [
	"bubble-man-rom", // generated / binary-ish JS
	"cue.mod",
	"wasm", // vendored wasm blobs beside life-lab
	"vendor-wasm",
	// XCTest suites force-unwrap fixtures constantly.
	"PlaygroundTests",
	"PlaygroundUITests",
]

// Keep the per-file parse timeout; hang defense still matters.
// Cumulative memory_budget is left unset (unlimited).
parse_timeout_ms: 5000
