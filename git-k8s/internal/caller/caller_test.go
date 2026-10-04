package caller

import (
	"errors"
	"net/http/httptest"
	"testing"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/kube"
)

func TestIdentify(t *testing.T) {
	repo := &gitk8s.GitRepository{Object: kube.Meta("app", nil)}
	world := []any{
		kube.FakeToken{
			Token:     "gofmt",
			User:      kube.UserInfo{Username: "system:serviceaccount:check-gofmt:check-gofmt"},
			Audiences: []string{gitk8s.MirrorAudience},
		},
		kube.FakeToken{
			Token: "pod",
			User: kube.UserInfo{
				Username: "system:serviceaccount:team:default",
				Extra:    map[string][]string{podNameExtra: {"gotest-1"}},
			},
			Audiences: []string{gitk8s.MirrorAudience},
		},
		kube.FakeToken{Token: "api", User: kube.UserInfo{Username: "system:serviceaccount:check-gofmt:check-gofmt"}},
		kube.FakeToken{Token: "person", User: kube.UserInfo{Username: "jane@example.com"}, Audiences: []string{gitk8s.MirrorAudience}},
	}
	for _, tc := range []struct {
		name, header string
		want         Caller
		check        string
	}{
		{name: "check", header: "Bearer gofmt", want: Caller{Namespace: "check-gofmt", Name: "check-gofmt"}, check: "gofmt"},
		{name: "lowercase scheme", header: "bearer gofmt", want: Caller{Namespace: "check-gofmt", Name: "check-gofmt"}, check: "gofmt"},
		{name: "pod", header: "Bearer pod", want: Caller{Namespace: "team", Name: "default", Pod: "gotest-1"}},
		{name: "no header"},
		{name: "basic auth", header: "Basic Z2l0OnB3"},
		{name: "unknown token", header: "Bearer nope"},
		{name: "the API server's audience", header: "Bearer api"},
		{name: "not a service account", header: "Bearer person"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			ctx, _ := kube.Fake(t.Context(), repo, world...)
			r := httptest.NewRequest("GET", "/", nil)
			if tc.header != "" {
				r.Header.Set("Authorization", tc.header)
			}
			got, err := Identify(ctx, r, gitk8s.MirrorAudience)
			if tc.want == (Caller{}) {
				if !errors.Is(err, ErrUnauthenticated) {
					t.Errorf("Identify = %+v, %v; want an error that wraps ErrUnauthenticated", got, err)
				}
				return
			}
			if err != nil || got != tc.want {
				t.Fatalf("Identify = %+v, %v; want %+v", got, err, tc.want)
			}
			if check, ok := got.Check(); check != tc.check || ok != (tc.check != "") {
				t.Errorf("Check() = %q, %v; want %q", check, ok, tc.check)
			}
		})
	}
}

func TestCheck(t *testing.T) {
	for c, want := range map[Caller]string{
		{Namespace: "check-gofmt", Name: "check-gofmt"}: "gofmt",
		{Namespace: "team", Name: "check-gofmt"}:        "",
		{Namespace: "check-", Name: "check-"}:           "",
		{Namespace: "git-k8s", Name: "git-k8s"}:         "",
	} {
		if got, ok := c.Check(); got != want || ok != (want != "") {
			t.Errorf("%v.Check() = %q, %v; want %q", c, got, ok, want)
		}
	}
}
