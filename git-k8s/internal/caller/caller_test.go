package caller

import (
	"errors"
	"net/http/httptest"
	"testing"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/kube"
)

func TestIdentify(t *testing.T) {
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
				Extra:    map[string][]string{podNameExtra: {"gotest-1"}, podUIDExtra: {"uid-1"}},
			},
			Audiences: []string{gitk8s.MirrorAudience},
		},
		kube.FakeToken{
			Token: "pod-without-uid",
			User: kube.UserInfo{
				Username: "system:serviceaccount:team:default",
				Extra:    map[string][]string{podNameExtra: {"gotest-1"}},
			},
			Audiences: []string{gitk8s.MirrorAudience},
		},
		kube.FakeToken{Token: "api", User: kube.UserInfo{Username: "system:serviceaccount:check-gofmt:check-gofmt"}},
		kube.FakeToken{Token: "person", User: kube.UserInfo{Username: "jane@example.com"}, Audiences: []string{gitk8s.MirrorAudience}},
	}
	entries := map[string]string{"check-gofmt.check-gofmt": "gofmt"}
	for _, tc := range []struct {
		name, header string
		want         Caller
		check        string
	}{
		{name: "check", header: "Bearer gofmt", want: Caller{Namespace: "check-gofmt", Name: "check-gofmt"}, check: "gofmt"},
		{name: "lowercase scheme", header: "bearer gofmt", want: Caller{Namespace: "check-gofmt", Name: "check-gofmt"}, check: "gofmt"},
		{name: "pod", header: "Bearer pod", want: Caller{Namespace: "team", Name: "default", Pod: "gotest-1", PodUID: "uid-1"}},
		{name: "pod without a UID", header: "Bearer pod-without-uid", want: Caller{Namespace: "team", Name: "default"}},
		{name: "no header"},
		{name: "basic auth", header: "Basic Z2l0OnB3"},
		{name: "unknown token", header: "Bearer nope"},
		{name: "the API server's audience", header: "Bearer api"},
		{name: "not a service account", header: "Bearer person"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			ctx, _ := kube.FakeRequest(t.Context(), world...)
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
				t.Fatalf("Identify = %#v, %v; want %#v", got, err, tc.want)
			}
			if check, ok := got.Check(entries); check != tc.check || ok != (tc.check != "") {
				t.Errorf("Check(%v) = %q, %v; want %q", entries, check, ok, tc.check)
			}
		})
	}
}

func TestCheck(t *testing.T) {
	gofmt := Caller{Namespace: "check-gofmt", Name: "check-gofmt"}
	bot := Caller{Namespace: "checks", Name: "bot"}
	core := Caller{Namespace: "git-k8s", Name: "git-k8s"}
	for _, tc := range []struct {
		name    string
		c       Caller
		entries map[string]string
		want    string
	}{
		{name: "generate's service account for a check, with an entry", c: gofmt, entries: map[string]string{"check-gofmt.check-gofmt": "gofmt"}, want: "gofmt"},
		{name: "generate's service account for a check, without an entry", c: gofmt},
		{name: "generate's service account for a check that runs elsewhere", c: Caller{Namespace: "check-approval", Name: "check-approval"}, entries: map[string]string{"checks.check-approval": "approval"}},
		{name: "a check's name in another namespace", c: Caller{Namespace: "team", Name: "check-gofmt"}, entries: map[string]string{"check-gofmt.check-gofmt": "gofmt"}},
		{name: "a service account named check-", c: Caller{Namespace: "check-", Name: "check-"}},
		{name: "the core program", c: core},
		{name: "a service account with an entry", c: bot, entries: map[string]string{"checks.bot": "bot"}, want: "bot"},
		{name: "a service account without an entry", c: bot, entries: map[string]string{"checks.other": "bot"}},
		{name: "an entry that names another check", c: gofmt, entries: map[string]string{"check-gofmt.check-gofmt": "risk"}, want: "risk"},
		{name: "an empty entry", c: gofmt, entries: map[string]string{"check-gofmt.check-gofmt": ""}},
		{name: "an entry for the core program", c: core, entries: map[string]string{"git-k8s.git-k8s": "gofmt"}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			if got, ok := tc.c.Check(tc.entries); got != tc.want || ok != (tc.want != "") {
				t.Errorf("%v.Check(%v) = %q, %v; want %q", tc.c, tc.entries, got, ok, tc.want)
			}
		})
	}
}
