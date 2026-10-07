package main

import (
	"encoding/json"
	"flag"
	"net/http"
	"net/http/httptest"
	"net/http/httputil"
	"net/url"
	"slices"
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

// reconcile runs the check on a branch whose copy a server serves like the
// mirror: at /NAMESPACE/NAME.git, to requests with a token from
// kube.RequestToken. The -mirror flag points to that server until the test
// ends.
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
	upstream, err := url.Parse(srv.URL)
	if err != nil {
		t.Fatal(err)
	}
	proxy := httputil.NewSingleHostReverseProxy(upstream)
	mirror := httptest.NewServer(http.HandlerFunc(func(rw http.ResponseWriter, r *http.Request) {
		path, ok := strings.CutPrefix(r.URL.Path, "/default/")
		switch {
		case !strings.HasPrefix(r.Header.Get("Authorization"), "Bearer fake-token-"):
			http.Error(rw, "send a token for the mirror", http.StatusUnauthorized)
		case !ok:
			http.NotFound(rw, r)
		default:
			r.URL.Path = "/" + path
			proxy.ServeHTTP(rw, r)
		}
	}))
	t.Cleanup(mirror.Close)
	t.Cleanup(func() { flag.Set("mirror", gitk8s.MirrorURL) })
	if err := flag.Set("mirror", mirror.URL); err != nil {
		t.Fatal(err)
	}
	b := &Branch{Object: kube.Meta("app-c-x", nil)}
	b.Namespace = "default"
	b.Spec = gitk8s.TrackedBranchSpec{
		Repository: "app", Branch: "c/x", Head: head, Parent: "main", ParentHead: main,
		Merge: &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{{Name: "review", MayPush: mayPush}}},
	}
	repo, _ := srv.Repository("app")
	ctx, rec := kube.Fake(t.Context(), b, repo)
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

func TestAgentPodsFetchFromTheMirror(t *testing.T) {
	defer func(r *agent.Runner) { runner = r }(runner)
	runner = &agent.Runner{Name: "review", Image: "agent-runner", GitImage: "git", Backend: "fake", Model: "composer-2.5", Secret: "cursor-api-key", Timeout: time.Minute}
	_, rec := reconcile(t, false)
	pods := kube.Owned[agent.Pod](rec)
	if len(pods) != 1 {
		t.Fatalf("%d Pods, want one", len(pods))
	}
	env := map[string]string{}
	var secrets []string
	for _, e := range pods[0].Spec.InitContainers[0].Env {
		if e.ValueFrom != nil && e.ValueFrom.SecretKeyRef != nil {
			secrets = append(secrets, e.ValueFrom.SecretKeyRef.Name)
		}
		env[e.Name] = e.Value
	}
	if want := flag.Lookup("mirror").Value.String() + "/default/app.git"; env["URL"] != want || env["TOKEN_FILE"] == "" {
		t.Errorf("the prepare container fetches %q with token file %q, want %q with a token for the mirror", env["URL"], env["TOKEN_FILE"], want)
	}
	if !slices.Equal(secrets, []string{"cursor-api-key"}) {
		t.Errorf("the prepare container reads Secrets %q, want only the API key's", secrets)
	}
}
