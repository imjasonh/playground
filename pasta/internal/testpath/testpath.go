// Package testpath reports whether a file is test code, by the path
// conventions of the languages pasta supports.
package testpath

import (
	"path/filepath"
	"regexp"
)

var testPathRe = regexp.MustCompile(
	`(^|/)(tests?|__tests__|testdata|spec|specs|e2e)(/)|(_test\.(go|rs|py))$|(\.test\.|\.spec\.|_test\.|_spec\.|test_[^/]*\.py$)`)

// Is reports whether the file at path is test code: a file in a test
// directory such as tests/, __tests__/, testdata/, spec/, or e2e/, or a
// test file such as foo_test.go, test_foo.py, or foo.spec.ts.
func Is(path string) bool {
	return testPathRe.MatchString(filepath.ToSlash(path))
}
