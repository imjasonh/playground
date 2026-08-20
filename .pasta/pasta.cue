// Playground monorepo pasta project config.
// Every analyzer under pasta/analyzers is enrolled via
// `.pasta/examples` → `pasta/analyzers`. Disable noisy ones here
// rather than omitting that symlink.

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

	// Mixed-precedence arithmetic is idiomatic in shaders, games, and HTML.
	"arith_parens",
	// Libraries and CLIs export helpers that this repo's other apps never call.
	"go_unused_export",
	// `if err != nil { return err }` is the Go style in this tree.
	"go_iferr",
	// Tests and local servers bind 127.0.0.1 / localhost on purpose.
	"hardcoded_localhost",
	// Fallback `100vh` then `100dvh` is a real browser-compat pattern here.
	"css_duplicate_property",
	// Worker and CLI tests compare JSON bools with `assert_eq!(x, true)`.
	"rust_bool_assert_comparison",

	// Fact lookup is file-blind: a const/fn/import in one app flags
	// assignments to the same name in another when ./... is one group.
	"js_no_const_assign",
	"js_no_func_assign",
	"js_no_class_assign",
	"js_no_import_assign",

	// Structural approximations that flood playground JS (trailing commas,
	// test literals, sequential awaits).
	"js_no_sparse_arrays",
	"js_no_constant_binary_expression",
	"js_no_await_in_loop",
	"js_preserve_caught_error",
	"js_no_control_regex",
	"js_no_setter_return",
	"js_no_empty",
	"js_no_unsafe_optional_chaining",
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
