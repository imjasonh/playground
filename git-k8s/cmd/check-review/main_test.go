package main

import (
	"encoding/json"
	"strings"
	"testing"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/agent"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/kube"
)

func reconcile(t *testing.T, mayPush bool) (*Branch, *kube.Recorder) {
	t.Helper()
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	w.Write("a.txt", "one\n")
	main := w.Commit("main")
	w.Push("main")
	w.Branch("c/x", main)
	w.Write("a.txt", "two\n")
	head := w.Commit("change")
	w.Push("c/x")
	b := &Branch{Object: kube.Meta("app-c-x", nil)}
	b.Namespace = "default"
	b.Spec = gitk8s.GitBranchSpec{
		Repository: "app", Branch: "c/x", Head: head, Parent: "main", ParentHead: main,
		Merge: &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{{Name: "review", MayPush: mayPush}}},
	}
	repo, secret := srv.Repository("app")
	ctx, rec := kube.Fake(t.Context(), b, repo, secret)
	cfg := &checks.Config{CacheDir: t.TempDir(), Identity: git.Identity{Name: "git-k8s", Email: "git-k8s@example.com"}}
	if err := checks.NewReconciler[Branch](check, cfg).Reconcile(ctx, b); err != nil {
		t.Fatal(err)
	}
	return b, rec
}

func TestNeedsAnAgentImage(t *testing.T) {
	b, rec := reconcile(t, false)
	if res := b.Status.Checks.Result; res.State != gitk8s.Running || !strings.Contains(res.Message, "set -agent-image") || len(kube.Owned[agent.Pod](rec)) != 0 {
		t.Errorf("result = %+v, want Running without a Pod", res)
	}
}

func TestEditsOnlyWhenItMayPush(t *testing.T) {
	defer func(r *agent.Runner) { runner = r }(runner)
	runner = &agent.Runner{Name: "review", Image: "agent-runner", GitImage: "git", Backend: "fake", Model: "composer-2.5", Secret: "cursor-api-key", Timeout: time.Minute}
	for _, mayPush := range []bool{false, true} {
		b, rec := reconcile(t, mayPush)
		pods := kube.Owned[agent.Pod](rec)
		if res := b.Status.Checks.Result; res.State != gitk8s.Running || len(pods) != 1 {
			t.Fatalf("result = %+v and %d Pods, want Running with one Pod", res, len(pods))
		}
		var task struct {
			Instructions string `json:"instructions"`
			Edit         bool   `json:"edit"`
		}
		if err := json.Unmarshal([]byte(pods[0].Spec.InitContainers[1].Env[0].Value), &task); err != nil {
			t.Fatal(err)
		}
		if task.Edit != mayPush || task.Instructions != instructions {
			t.Errorf("with mayPush %t, the agent's task = %+v", mayPush, task)
		}
	}
}
