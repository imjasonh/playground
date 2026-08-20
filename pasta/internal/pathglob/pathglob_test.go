package pathglob

import "testing"

func TestMatch(t *testing.T) {
	cases := []struct {
		pat, name string
		want      bool
	}{
		{pat: "ios/**/project.yml", name: "ios/project.yml", want: true},
		{pat: "ios/**/project.yml", name: "ios/nested/project.yml", want: true},
		{pat: "ios/**/project.yml", name: "./ios/project.yml", want: true},
		{pat: "ios/**/project.yml", name: "/abs/ios/project.yml", want: true},
		{pat: "ios/**/project.yml", name: "hello-macos/project.yml", want: false},
		{pat: "ios/**/project.yml", name: "onramp/project.yml", want: false},
		{pat: "ios/**/project.yml", name: "ios/project.yaml", want: false},
		{pat: "ios/project.yml", name: "ios/project.yml", want: true},
		{pat: "ios/project.yml", name: "hello-macos/project.yml", want: false},
		{pat: "project.yml", name: "ios/project.yml", want: true},
		{pat: "*.yml", name: "ios/project.yml", want: true},
		{pat: "*.yml", name: "ios/project.yaml", want: false},
		{pat: "**/*.yml", name: "ios/foo/project.yml", want: true},
		{pat: "ios/**", name: "ios/project.yml", want: true},
		{pat: "ios/**", name: "ios", want: true},
		{pat: "", name: "ios/project.yml", want: false},
	}
	for _, tc := range cases {
		got := Match(tc.pat, tc.name)
		if got != tc.want {
			t.Errorf("Match(%q, %q) = %v, want %v", tc.pat, tc.name, got, tc.want)
		}
	}
}

func TestValid(t *testing.T) {
	if err := Valid("ios/**/project.yml"); err != nil {
		t.Errorf("valid glob rejected: %v", err)
	}
	if err := Valid(""); err == nil {
		t.Error("empty glob should be invalid")
	}
	if err := Valid("   "); err == nil {
		t.Error("whitespace glob should be invalid")
	}
	if err := Valid("[unclosed"); err == nil {
		t.Error("malformed character class should be invalid")
	}
}
