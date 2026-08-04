package store

import "testing"

func TestIsPlatformDemo(t *testing.T) {
	t.Parallel()
	if !IsPlatformDemo("fortune") || IsPlatformDemo("myapp") {
		t.Fatal("demo map unexpected")
	}
}
