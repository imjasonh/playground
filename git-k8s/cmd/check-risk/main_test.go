package main

import (
	"strings"
	"testing"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/kube"
)

func rate(t *testing.T, files map[string]string) *gitk8s.CheckResult {
	t.Helper()
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	w.Write("README.md", "hello\n")
	main := w.Commit("main")
	w.Push("main")
	w.Branch("c/x", main)
	for path, content := range files {
		w.Write(path, content)
	}
	head := w.Commit("change")
	w.Push("c/x")

	b := &Branch{Object: kube.Meta("app-c-x", nil)}
	b.Namespace = "default"
	b.Spec = gitk8s.GitBranchSpec{
		Repository: "app", Branch: "c/x", Head: head, Parent: "main", ParentHead: main,
		Merge: &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{{Name: "risk"}}},
	}
	repo, _ := srv.Repository("app")
	ctx, _ := kube.Fake(t.Context(), b, repo)
	c := check
	c.Remote = srv.RemoteFor
	if err := checks.NewReconciler[Branch](c, &checks.Config{CacheDir: t.TempDir()}).Reconcile(ctx, b); err != nil {
		t.Fatal(err)
	}
	return b.Status.Checks.Result
}

func TestRisk(t *testing.T) {
	*maxLines, *sensitive = 10, "auth/**, **/*.pem"
	for _, c := range []struct {
		name   string
		files  map[string]string
		level  string
		reason string
	}{
		{"small", map[string]string{"docs/a.md": "a\nb\n"}, "low", "changes 2 lines in 1 files"},
		{"big", map[string]string{"big.txt": strings.Repeat("x\n", 11)}, "high", "changes 11 lines, more than 10"},
		{"sensitive", map[string]string{"auth/policy.go": "package auth\n"}, "high", "touches auth/policy.go"},
		{"sensitive glob", map[string]string{"certs/server.pem": "key\n"}, "high", "touches certs/server.pem"},
	} {
		t.Run(c.name, func(t *testing.T) {
			res := rate(t, c.files)
			if res.State != gitk8s.Passed || res.Outputs["level"] != c.level || !strings.Contains(res.Message, c.reason) {
				t.Errorf("result = %+v, want level %s and %q", res, c.level, c.reason)
			}
			if res.ParentCommit == "" {
				t.Error("risk results depend on the parent's head")
			}
		})
	}
}
