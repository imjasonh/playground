package main

import "testing"

func TestParseAnnotations(t *testing.T) {
	got, err := parseAnnotations([]string{
		"org.opencontainers.image.revision=abc123",
		// Values contain '=' more often than you would like; only the first
		// separator counts.
		"org.opencontainers.image.source=https://example.test/?a=b",
		"empty=",
	})
	if err != nil {
		t.Fatalf("parseAnnotations: %v", err)
	}
	want := map[string]string{
		"org.opencontainers.image.revision": "abc123",
		"org.opencontainers.image.source":   "https://example.test/?a=b",
		"empty":                             "",
	}
	for key, value := range want {
		if got[key] != value {
			t.Errorf("%s = %q, want %q", key, got[key], value)
		}
	}
}

func TestMalformedAnnotationIsRefused(t *testing.T) {
	for _, pair := range []string{"novalue", "=novalue"} {
		if _, err := parseAnnotations([]string{pair}); err == nil {
			t.Errorf("parseAnnotations accepted %q", pair)
		}
	}
}
