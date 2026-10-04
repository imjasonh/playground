package checks

import (
	"context"
	"encoding/json"
	"fmt"
	"net/http"
	"net/http/httptest"
	"strings"
	"sync"
	"testing"
	"time"
	"unicode/utf8"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/kube"
)

// view is a check's view of a GitBranch, like the ones that check programs
// declare.
type view struct {
	kube.Object `kube:"apiVersion=git-k8s.imjasonh.com/v1alpha1,kind=GitBranch,plural=gitbranches,scope=Namespaced"`
	Spec        gitk8s.GitBranchSpec `json:"spec"`
	Status      struct {
		Checks struct {
			Result *gitk8s.CheckResult `json:"lint,omitempty"`
		} `json:"checks,omitzero"`
	} `json:"status,omitzero"`
}

func (v *view) Parts() (*kube.ObjectMeta, *gitk8s.GitBranchSpec, **gitk8s.CheckResult) {
	return &v.ObjectMeta, &v.Spec, &v.Status.Checks.Result
}

type received struct {
	uri, auth string
	result    gitk8s.CheckResult
}

// endpoint is a results endpoint that answers with codes in order, and
// then with 204.
type endpoint struct {
	mu       sync.Mutex
	codes    []int
	received []received
}

func (e *endpoint) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	var res gitk8s.CheckResult
	_ = json.NewDecoder(r.Body).Decode(&res)
	e.mu.Lock()
	defer e.mu.Unlock()
	e.received = append(e.received, received{uri: r.URL.RequestURI(), auth: r.Header.Get("Authorization"), result: res})
	code := http.StatusNoContent
	if len(e.codes) > 0 {
		code, e.codes = e.codes[0], e.codes[1:]
	}
	if code == http.StatusNoContent {
		w.WriteHeader(code)
		return
	}
	http.Error(w, http.StatusText(code), code)
}

func (e *endpoint) requests() []received {
	e.mu.Lock()
	defer e.mu.Unlock()
	return append([]received(nil), e.received...)
}

type sendFixture struct {
	branch  *branch
	view    *view
	repo    *gitk8s.GitRepository
	verdict Verdict
	runs    int
	r       kube.Reconciler[view]
	s       *sender
}

// newSendFixture returns a fixture whose check, lint, returns the
// fixture's verdict for c/x at generation 4, and sends results to e.
func newSendFixture(t *testing.T, e *endpoint) *sendFixture {
	srv := httptest.NewServer(e)
	t.Cleanup(srv.Close)
	f := &sendFixture{branch: &branch{Object: kube.Meta("app-c-x", nil)}, view: &view{Object: kube.Meta("app-c-x", nil)}}
	f.branch.Namespace, f.view.Namespace, f.view.Generation = "default", "default", 4
	f.view.Spec = gitk8s.GitBranchSpec{
		Repository: "app", Branch: "c/x", Head: "h1", Parent: "main", ParentHead: "p1",
		Merge: &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{{Name: "lint"}}},
	}
	f.branch.Spec = f.view.Spec
	f.repo = &gitk8s.GitRepository{Object: kube.Meta("app", nil)}
	f.repo.Namespace = "default"
	check := Check{Name: "lint", Run: func(context.Context, *Input) (Verdict, error) {
		f.runs++
		return f.verdict, nil
	}}
	cfg := &Config{ResultsURL: srv.URL + "/results/"}
	f.r = NewReconciler[view](check, cfg)
	f.s = &sender{check: "lint", cfg: cfg, client: srv.Client(), delay: time.Microsecond}
	return f
}

func (f *sendFixture) context(t *testing.T) context.Context {
	ctx, _ := kube.Fake(t.Context(), f.branch, f.view, f.repo)
	return ctx
}

func (f *sendFixture) runAndSend(ctx context.Context) error {
	return runAndSend[view](ctx, f.r, f.s, f.branch)
}

func TestSendsNewResults(t *testing.T) {
	e := &endpoint{}
	f := newSendFixture(t, e)
	f.verdict = Pass("clean")
	if err := f.runAndSend(f.context(t)); err != nil {
		t.Fatal(err)
	}
	got := e.requests()
	want := received{
		uri: "/results/default/app-c-x/lint?generation=4", auth: "Bearer fake-token-1",
		result: gitk8s.CheckResult{Commit: "h1", State: gitk8s.Passed, Message: "clean"},
	}
	if len(got) != 1 || got[0].uri != want.uri || got[0].auth != want.auth || !got[0].result.Equal(&want.result) {
		t.Fatalf("received %+v, want %+v", got, want)
	}

	t.Log("Once the check's view shows the result, the check doesn't run or send it again.")
	f.view.Status.Checks.Result = &got[0].result
	if err := f.runAndSend(f.context(t)); err != nil {
		t.Fatal(err)
	}
	if n := len(e.requests()); n != 1 || f.runs != 1 {
		t.Errorf("%d runs sent %d results, want 1 run and 1 result", f.runs, n)
	}

	t.Log("A new head runs the check again, and the new result has the spec's generation.")
	f.view.Spec.Head, f.view.Generation = "h2", 5
	f.verdict = Fail("x.go isn't formatted")
	if err := f.runAndSend(f.context(t)); err != nil {
		t.Fatal(err)
	}
	got = e.requests()
	if len(got) != 2 || got[1].uri != "/results/default/app-c-x/lint?generation=5" || got[1].result.Commit != "h2" || got[1].result.State != gitk8s.Failed {
		t.Errorf("received %+v, want a Failed result for h2 at generation 5", got)
	}
}

func TestSendsNothingWhenNotListed(t *testing.T) {
	e := &endpoint{}
	f := newSendFixture(t, e)
	f.view.Spec.Merge.Checks[0].Name = "other"
	f.view.Status.Checks.Result = &gitk8s.CheckResult{Commit: "h0", State: gitk8s.Passed}
	if err := f.runAndSend(f.context(t)); err != nil {
		t.Fatal(err)
	}
	if got := e.requests(); len(got) != 0 || f.runs != 0 {
		t.Errorf("%d runs sent %+v; the core program removes the result of a check that the policy doesn't list", f.runs, got)
	}
}

// The framework replaces a result that the core program doesn't accept
// with an Error result that says why, so that the branch shows it.
func TestSendsErrorForInvalidResult(t *testing.T) {
	outputs := map[string]string{}
	for i := range gitk8s.MaxOutputs + 1 {
		outputs[fmt.Sprintf("output-%d", i)] = "v"
	}
	for _, tc := range []struct {
		name    string
		verdict Verdict
		msg     string
	}{
		{"17 outputs", Verdict{State: gitk8s.Passed, Outputs: outputs}, "the core program doesn't accept the check's result: the result has more than 16 outputs"},
		{"no state", Verdict{Message: "done"}, `the core program doesn't accept the check's result: state "" isn't`},
	} {
		t.Run(tc.name, func(t *testing.T) {
			e := &endpoint{}
			f := newSendFixture(t, e)
			f.verdict = tc.verdict
			if err := f.runAndSend(f.context(t)); err != nil {
				t.Fatal(err)
			}
			got := e.requests()
			if len(got) != 1 || got[0].result.State != gitk8s.Error || !strings.HasPrefix(got[0].result.Message, tc.msg) || got[0].result.Validate() != nil {
				t.Errorf("received %+v, want a valid Error result whose message starts with %q", got, tc.msg)
			}
		})
	}
}

func TestSendAnswers(t *testing.T) {
	for _, tc := range []struct {
		name     string
		codes    []int
		requests int
		err      string
	}{
		{"retries 503s with the same token", []int{503, 503}, 3, ""},
		{"gives up after 10 503s", []int{503, 503, 503, 503, 503, 503, 503, 503, 503, 503}, sendAttempts, "didn't write the lint check's result"},
		{"drops a result that the core program doesn't take", []int{409}, 1, ""},
		{"stops on other errors", []int{500}, 1, "Internal Server Error"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			e := &endpoint{codes: tc.codes}
			f := newSendFixture(t, e)
			f.verdict = Pass("clean")
			err := f.runAndSend(f.context(t))
			if tc.err == "" && err != nil || tc.err != "" && (err == nil || !strings.Contains(err.Error(), tc.err)) {
				t.Errorf("err = %v, want %q", err, tc.err)
			}
			got := e.requests()
			if len(got) != tc.requests {
				t.Errorf("sent %d requests, want %d", len(got), tc.requests)
			}
			for _, r := range got {
				if r.auth != "Bearer fake-token-1" {
					t.Errorf("Authorization = %q; reuse the token", r.auth)
				}
			}
		})
	}
}

func TestRejectedResultIsPermanent(t *testing.T) {
	f := newSendFixture(t, &endpoint{codes: []int{400}})
	f.verdict = Pass("clean")
	if err := f.runAndSend(f.context(t)); !kube.IsPermanent(err) {
		t.Errorf("err = %v, want a permanent error, because sending the same result again won't help", err)
	}
}

func TestRefusedTokenIsReplaced(t *testing.T) {
	e := &endpoint{codes: []int{401}}
	f := newSendFixture(t, e)
	f.verdict = Pass("clean")
	ctx := f.context(t)
	if err := f.runAndSend(ctx); err == nil || !strings.Contains(err.Error(), "Unauthorized") {
		t.Fatalf("err = %v, want Unauthorized", err)
	}
	if err := f.runAndSend(ctx); err != nil {
		t.Fatal(err)
	}
	if got := e.requests(); len(got) != 2 || got[1].auth != "Bearer fake-token-2" {
		t.Errorf("received %+v, want a new token after the first was refused", got)
	}
}

func TestSendRetriesUnreachableEndpoint(t *testing.T) {
	f := newSendFixture(t, &endpoint{})
	f.s.cfg = &Config{ResultsURL: "http://127.0.0.1:1/results"}
	f.verdict = Pass("clean")
	if err := f.runAndSend(f.context(t)); err == nil || kube.IsPermanent(err) {
		t.Errorf("err = %v, want an error that kube retries", err)
	}
}

func TestShorten(t *testing.T) {
	for _, tc := range []struct {
		in   string
		n    int
		want string
	}{
		{"short", 10, "short"},
		{"exactly 10", 10, "exactly 10"},
		{"a bit too long", 10, "a bit t..."},
		{"ééééé", 8, "éé..."},
		{"invalid \xff byte", 100, "invalid \uFFFD byte"},
		{"\xff\xff\xff\xff", 8, "\uFFFD"},
		{"ab\xffcd\xffef\xff", 7, "ab..."},
	} {
		got := shorten(tc.in, tc.n)
		if got != tc.want || len(got) > tc.n || !utf8.ValidString(got) {
			t.Errorf("shorten(%q, %d) = %q, want %q", tc.in, tc.n, got, tc.want)
		}
	}
	if truncateOutputs(nil) != nil {
		t.Error("truncateOutputs(nil) isn't nil")
	}
	if got := truncateOutputs(map[string]string{"files": strings.Repeat("a.go ", 300)}); len(got["files"]) != gitk8s.MaxOutputValueLength {
		t.Errorf("output of %d bytes, want %d", len(got["files"]), gitk8s.MaxOutputValueLength)
	}
}
