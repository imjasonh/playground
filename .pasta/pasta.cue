// Playground monorepo pasta project config.
// Every analyzer under pasta/analyzers is enrolled by
// `.pasta/examples` → `pasta/analyzers`.

package pasta_project

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

// XcodeGen uses YES/NO for build settings. yaml_truthy would rewrite
// those to true/false, which Xcode does not accept. Other YAML rules
// still run on those files.
//
// pstack scripts under .cursor/skills/ are upstream copies. Do not
// rewrite them to satisfy playground JS rules.
disabled_on: {
	yaml_truthy: ["**/project.yml"]
	js_preserve_caught_error: ["**/.cursor/skills/**"]
	js_no_constant_condition_while: ["**/.cursor/skills/**"]
}

// Keep the per-file parse timeout; hang defense still matters.
// Cumulative memory_budget is left unset (unlimited).
parse_timeout_ms: 5000
