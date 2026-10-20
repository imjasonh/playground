package main

import (
	"testing"
)

func TestGreet(t *testing.T) {
	t.Parallel()

	tests := []struct {
		name     string
		greeting string
		user     string
		want     string
	}{
		{name: "named user", greeting: "hello", user: "ada", want: "hello, ada\n"},
		{name: "empty user", greeting: "hello", user: "", want: "hello, friend\n"},
	}
	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			t.Parallel()
			got := greet(tc.greeting, tc.user)
			if got != tc.want {
				t.Fatalf("greet(%q, %q) = %q, want %q", tc.greeting, tc.user, got, tc.want)
			}
		})
	}
}
