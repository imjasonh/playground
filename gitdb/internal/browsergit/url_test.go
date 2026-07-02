package browsergit

import "testing"

func TestNormalizeRepositoryURL(t *testing.T) {
	tests := []struct {
		input string
		want  string
	}{
		{"imjasonh/playground", "https://github.com/imjasonh/playground.git"},
		{"https://github.com/imjasonh/playground", "https://github.com/imjasonh/playground.git"},
		{"https://example.com/a/repo.git/", "https://example.com/a/repo.git"},
		{"http://127.0.0.1:8080/repo.git", "http://127.0.0.1:8080/repo.git"},
	}
	for _, test := range tests {
		got, err := NormalizeRepositoryURL(test.input)
		if err != nil {
			t.Fatalf("NormalizeRepositoryURL(%q): %v", test.input, err)
		}
		if got != test.want {
			t.Errorf("NormalizeRepositoryURL(%q) = %q, want %q", test.input, got, test.want)
		}
	}
}

func TestNormalizeRepositoryURLRejectsUnsupportedInputs(t *testing.T) {
	for _, input := range []string{"", "repo", "ssh://git@example.com/repo", "https://example.com", "https://u:p@example.com/repo"} {
		if _, err := NormalizeRepositoryURL(input); err == nil {
			t.Errorf("NormalizeRepositoryURL(%q) unexpectedly succeeded", input)
		}
	}
}

func TestProxyRepositoryURL(t *testing.T) {
	repository := "https://github.com/imjasonh/playground.git"
	got, err := ProxyRepositoryURL(repository, "https://cors.isomorphic-git.org/")
	if err != nil {
		t.Fatal(err)
	}
	want := "https://cors.isomorphic-git.org/github.com/imjasonh/playground.git"
	if got != want {
		t.Errorf("ProxyRepositoryURL() = %q, want %q", got, want)
	}

	direct, err := ProxyRepositoryURL(repository, "")
	if err != nil {
		t.Fatal(err)
	}
	if direct != repository {
		t.Errorf("direct URL = %q, want %q", direct, repository)
	}
}
