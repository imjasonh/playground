package mirror_test

import (
	"flag"
	"testing"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/mirror"
	"github.com/imjasonh/playground/kube"
)

func TestRemote(t *testing.T) {
	repo := &gitk8s.RepositoryView{Object: kube.Meta("app", nil)}
	repo.Namespace = "team"
	ctx, _ := kube.Fake(t.Context(), repo)
	r, err := mirror.Remote(ctx, repo)
	if err != nil {
		t.Fatal(err)
	}
	if want := "http://git-k8s.git-k8s.svc/team/app.git"; r.URL != want {
		t.Errorf("URL = %q, want %q", r.URL, want)
	}
	if r.Auth == nil || r.Auth.Token == "" || r.Auth.Password != "" {
		t.Fatalf("Auth = %+v, want only a token", r.Auth)
	}
	review, err := kube.ReviewToken(ctx, r.Auth.Token, gitk8s.MirrorAudience)
	if err != nil || !review.Authenticated {
		t.Errorf("ReviewToken = %+v, %v; want a token for the mirror's audience", review, err)
	}

	t.Cleanup(func() { flag.Set("mirror", gitk8s.MirrorURL) })
	if err := flag.Set("mirror", "http://mirror.example:8080/"); err != nil {
		t.Fatal(err)
	}
	if r, err := mirror.Remote(ctx, repo); err != nil || r.URL != "http://mirror.example:8080/team/app.git" {
		t.Errorf("with -mirror set, Remote = %q, %v", r.URL, err)
	}
}
