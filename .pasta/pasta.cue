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

// Keep the per-file parse timeout; hang defense still matters.
// Cumulative memory_budget is left unset (unlimited).
parse_timeout_ms: 5000
