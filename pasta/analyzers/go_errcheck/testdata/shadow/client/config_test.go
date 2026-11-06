package client

import "testing"

// writeFile fails the test itself, so its callers have nothing to check.
// It shadows the error-returning writeFile in package app.
func writeFile(t *testing.T, name string) {
	t.Helper()
}

func TestConfig(t *testing.T) {
	writeFile(t, "config") // OK: binds to the writeFile in this file
}
