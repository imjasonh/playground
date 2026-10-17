package mirror_test

import (
	"flag"
	"strings"
	"testing"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/mirror"
	"github.com/imjasonh/playground/kube"
)

func TestRemote(t *testing.T) {
	repo := &gitk8s.Repository{Object: kube.Meta("app", nil)}
	repo.Namespace = "team"
	ctx, _ := kube.Fake(t.Context(), repo)
	r, err := mirror.Remote(ctx, gitk8s.CoreURL, repo)
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

	if r, err := mirror.Remote(ctx, "http://core.example:8080/", repo); err != nil || r.URL != "http://core.example:8080/team/app.git" {
		t.Errorf("with the core program at http://core.example:8080/, Remote = %q, %v", r.URL, err)
	}
}

// TestRegistersNoFlags checks that a program that links the package, such as
// a check, can define any flag.
func TestRegistersNoFlags(t *testing.T) {
	flag.VisitAll(func(f *flag.Flag) {
		if !strings.HasPrefix(f.Name, "test.") {
			t.Errorf("linking the package registers -%s", f.Name)
		}
	})
}
