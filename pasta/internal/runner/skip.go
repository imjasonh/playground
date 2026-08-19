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
	".terraform":       true, // Terraform and OpenTofu providers and modules
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
	"testdata":         true, // analyzer / Go test fixtures
	"target":           true, // Rust build output
	"dist":             true,
	"build":            true,
	"coverage":         true,
	"test-results":     true,
	"DerivedData":      true, // Xcode
}

// IsGeneratedLockfile reports whether basename is a known generated
// package-manager lockfile that happens to use a language extension
// pasta understands (e.g. package-lock.json → json). These are not
// hand-written source and should not be linted during `./...` walks.
func IsGeneratedLockfile(basename string) bool {
	switch basename {
	case "package-lock.json", "npm-shrinkwrap.json":
		return true
	default:
		return false
	}
}
