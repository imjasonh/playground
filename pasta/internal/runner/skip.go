package runner

// DefaultSkipDirs are directory basenames pasta won't descend into
// during `./...` expansion. These are third-party dependency trees,
// VCS metadata, and rule directories — not first-party source. Pasta
// does not try to lint or rewrite vendored ecosystem packages (Go
// vendor/, JS node_modules/, Composer vendor/, CocoaPods, Python
// venvs, etc.); language tooling owns those trees.
var DefaultSkipDirs = map[string]bool{
	".git":             true,
	".pasta":           true,
	"vendor":           true, // Go modules, PHP Composer, and similar
	"node_modules":     true, // npm / yarn / pnpm
	"bower_components": true,
	"jspm_packages":    true,
	"Godeps":           true, // legacy Go
	"Pods":             true, // CocoaPods
	"Carthage":         true,
	".bundle":          true, // Ruby Bundler
	"venv":             true, // Python virtualenv
	".venv":            true,
	"site-packages":    true,
	"__pycache__":      true,
	".tox":             true,
	".nox":             true,
	"third_party":      true,
}
