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
	// Fork of benbjohnson/litestream. Keep it diffable against upstream.
	"litestream",
]

// XcodeGen uses YES/NO for build settings. yaml_truthy would rewrite
// those to true/false, which Xcode does not accept. Other YAML rules
// still run on those files.
//
// pstack scripts under .cursor/skills/ are upstream copies. Do not
// rewrite them to satisfy playground JS rules.
//
// Google JS and TS style allow `== null` / `!= null` as the nullish
// check. js_no_eq_null is the ESLint ban on that idiom.
//
// jest, Playwright, and other tool configs are required to default-export.
disabled_rules: ["js_no_eq_null"]
disabled_on: {
	yaml_truthy: ["**/project.yml"]
	js_preserve_caught_error: ["**/.cursor/skills/**"]
	js_no_constant_condition_while: ["**/.cursor/skills/**"]
	js_no_default_export: [
		"**/*.config.js",
		"**/*.config.mjs",
		"**/*.config.cjs",
		"**/*.config.ts",
		"**/*.config.tsx",
	]
}

// Keep the per-file parse timeout; hang defense still matters.
// Cumulative memory_budget is left unset (unlimited).
parse_timeout_ms: 5000
