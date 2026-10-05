package git

import (
	"os/exec"
	"strings"
	"testing"
)

func TestValidBranch(t *testing.T) {
	if _, err := exec.LookPath("git"); err != nil {
		t.Skip("git isn't installed")
	}
	for _, name := range []string{
		"main", "c/add", "feature/ünïcode", "v1.0", "a-b", "a/-b", "a@b", "@", "HEAD", "a.lockx",
		"-b", "--upload-pack=touch x",
		"", ".", "..", ".a", "a/.b", "a.", "a/b.", "a..b", "a.lock", "a/b.lock/c",
		"/a", "a/", "a//b", "a b", "a\tb", "a\nb", "a\x01b", "a\x7fb",
		"a~b", "a^b", "a:b", "a?b", "a*b", "a[b", "a\\b", "a@{b", "a{b",
	} {
		want := !strings.HasPrefix(name, "-") &&
			exec.Command("git", "check-ref-format", "refs/heads/"+name).Run() == nil
		if got := validBranch(name); got != want {
			t.Errorf("validBranch(%q) = %v, want %v", name, got, want)
		}
	}
}
