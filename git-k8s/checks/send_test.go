package checks

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"maps"
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
	err     error
	runs    int
	r       kube.Reconciler[view]
	s       *sender
}

// newSendFixture returns a fixture whose check, lint, returns the
// fixture's verdict and error for c/x at generation 4, and sends results to
// e.
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
		return f.verdict, f.err
	}}
	cfg := &Config{CoreURL: srv.URL + "/"}
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
		result: gitk8s.CheckResult{Commit: "h1", Scope: gitk8s.ScopeHead, State: gitk8s.Passed, Message: "clean"},
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
	f.view.Status.Checks.Result = &gitk8s.CheckResult{Commit: "h0", Scope: gitk8s.ScopeHead, State: gitk8s.Passed}
	if err := f.runAndSend(f.context(t)); err != nil {
		t.Fatal(err)
	}
	if got := e.requests(); len(got) != 0 || f.runs != 0 {
		t.Errorf("%d runs sent %+v; the core program removes the result of a check that the policy doesn't list", f.runs, got)
	}
}

type viewFunc func(context.Context, *view) error

func (f viewFunc) Reconcile(ctx context.Context, v *view) error { return f(ctx, v) }

// A check that passes its own reconciler to ForReconciler sends the result
// that the reconciler sets, and nothing when the reconciler clears it, as
// check-conflicts does on a branch without a parent.
func TestSendsTheResultOfItsOwnReconciler(t *testing.T) {
	e := &endpoint{}
	f := newSendFixture(t, e)
	check := f.r
	f.r = viewFunc(func(ctx context.Context, v *view) error {
		if v.Spec.Parent == "" {
			v.Status.Checks.Result = nil
			return nil
		}
		return check.Reconcile(ctx, v)
	})
	f.verdict = Pass("clean")
	if err := f.runAndSend(f.context(t)); err != nil {
		t.Fatal(err)
	}
	if got := e.requests(); len(got) != 1 || got[0].result.State != gitk8s.Passed {
		t.Fatalf("received %+v, want the check's Passed result", got)
	}

	t.Log("The reconciler clears the result of a branch without a parent, so the check sends nothing for it.")
	f.view.Spec.Parent, f.view.Spec.ParentHead = "", ""
	f.view.Status.Checks.Result = &gitk8s.CheckResult{Commit: "h1", Scope: gitk8s.ScopeHead, State: gitk8s.Running}
	if err := f.runAndSend(f.context(t)); err != nil {
		t.Fatal(err)
	}
	if got := e.requests(); len(got) != 1 || f.runs != 1 {
		t.Errorf("%d runs sent %d results, want 1 run and 1 result", f.runs, len(got))
	}
}

// A check that stopped setting FilesOnly runs again on its last result, and
// sends the new one even if only filesOnly changed, so that the old result
// stops counting for squashed and rebased commits.
func TestSendsResultWithoutFilesOnly(t *testing.T) {
	e := &endpoint{}
	f := newSendFixture(t, e)
	f.view.Status.Checks.Result = &gitk8s.CheckResult{Commit: "h1", Scope: gitk8s.ScopeHead, State: gitk8s.Passed, Message: "clean", FilesOnly: true}
	f.verdict = Pass("clean")
	if err := f.runAndSend(f.context(t)); err != nil {
		t.Fatal(err)
	}
	got := e.requests()
	want := gitk8s.CheckResult{Commit: "h1", Scope: gitk8s.ScopeHead, State: gitk8s.Passed, Message: "clean"}
	if f.runs != 1 || len(got) != 1 || !got[0].result.Equal(&want) {
		t.Errorf("%d runs sent %+v, want %+v", f.runs, got, want)
	}
}

// A check that can't run sends an Error result, and its reconcile still
// fails, so that kube runs the check again.
func TestSendsErrorAndFails(t *testing.T) {
	e := &endpoint{}
	f := newSendFixture(t, e)
	f.err = errors.New("can't fetch c/x")
	if err := f.runAndSend(f.context(t)); err == nil || !strings.Contains(err.Error(), "can't fetch c/x") || kube.IsPermanent(err) {
		t.Errorf("err = %v, want the check's error, which kube retries", err)
	}
	got := e.requests()
	want := gitk8s.CheckResult{Commit: "h1", Scope: gitk8s.ScopeHead, State: gitk8s.Error, Message: "can't fetch c/x"}
	if len(got) != 1 || !got[0].result.Equal(&want) {
		t.Errorf("received %+v, want %+v", got, want)
	}
}

// A check's reconcile of a branch that's gone succeeds, even if the check
// failed, because running the check again can't help. Only a 410 says that
// the branch is gone. A 404 can come from a wrong -core-url, so the
// reconcile fails with the check's error and the 404, and kube retries it.
func TestBranchGoneEndsReconcile(t *testing.T) {
	for code, want := range map[int][]string{
		http.StatusGone:     nil,
		http.StatusNotFound: {"can't fetch c/x", "Not Found"},
	} {
		e := &endpoint{codes: []int{code}}
		f := newSendFixture(t, e)
		f.err = errors.New("can't fetch c/x")
		err := f.runAndSend(f.context(t))
		if want == nil && err != nil {
			t.Errorf("after %d, err = %v, want none for a branch that's gone", code, err)
		}
		if want != nil && (err == nil || kube.IsPermanent(err)) {
			t.Errorf("after %d, err = %v, want an error that kube retries", code, err)
		}
		for _, s := range want {
			if err != nil && !strings.Contains(err.Error(), s) {
				t.Errorf("after %d, err = %v, want it to say %q", code, err, s)
			}
		}
		if got := e.requests(); len(got) != 1 || got[0].result.State != gitk8s.Error {
			t.Errorf("after %d, received %+v, want one Error result", code, got)
		}
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

func TestSendsNotesAndPod(t *testing.T) {
	e := &endpoint{}
	f := newSendFixture(t, e)
	f.verdict = Verdict{State: gitk8s.Running, Message: "testing", Pod: "lint-h1", Notes: map[string]string{"job": strings.Repeat("j", 2*gitk8s.MaxNoteValueLength)}}
	if err := f.runAndSend(f.context(t)); err != nil {
		t.Fatal(err)
	}
	got := e.requests()
	if len(got) != 1 || got[0].result.Pod != "lint-h1" || len(got[0].result.Notes["job"]) != gitk8s.MaxNoteValueLength || got[0].result.Validate() != nil {
		t.Errorf("received %+v, want a valid result with the Pod lint-h1 and the note job shortened to %d bytes", got, gitk8s.MaxNoteValueLength)
	}
}

// An Error result keeps the check's notes, so that a check that counts its
// runs in them, as agent does, doesn't count from zero after an error. It
// keeps the previous result's notes when the check fails to run or when the
// core program doesn't accept the verdict's notes.
func TestErrorResultsKeepNotes(t *testing.T) {
	previous := map[string]string{"runs": "3"}
	outputs, notes := map[string]string{}, map[string]string{}
	for i := range gitk8s.MaxOutputs + 1 {
		outputs[fmt.Sprintf("output-%d", i)] = "v"
	}
	for i := range gitk8s.MaxNotes + 1 {
		notes[fmt.Sprintf("note-%d", i)] = "v"
	}
	for _, tc := range []struct {
		name    string
		verdict Verdict
		err     error
		notes   map[string]string
	}{
		{"the check fails to run", Verdict{}, errors.New("no route to host"), previous},
		{"too many outputs", Verdict{State: gitk8s.Failed, Outputs: outputs, Notes: map[string]string{"runs": "4"}, Pod: "lint-h1"}, nil, map[string]string{"runs": "4"}},
		{"too many notes", Verdict{State: gitk8s.Passed, Notes: notes}, nil, previous},
		{"a Pod name that's too long", Verdict{State: gitk8s.Running, Notes: map[string]string{"runs": "4"}, Pod: strings.Repeat("p", gitk8s.MaxPodNameLength+1)}, nil, map[string]string{"runs": "4"}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			e := &endpoint{}
			f := newSendFixture(t, e)
			f.view.Status.Checks.Result = &gitk8s.CheckResult{Commit: "h0", Scope: gitk8s.ScopeHead, State: gitk8s.Failed, Notes: previous}
			f.verdict, f.err = tc.verdict, tc.err
			if err := f.runAndSend(f.context(t)); !errors.Is(err, tc.err) {
				t.Errorf("err = %v, want %v", err, tc.err)
			}
			got := e.requests()
			if len(got) != 1 || got[0].result.State != gitk8s.Error || !maps.Equal(got[0].result.Notes, tc.notes) || got[0].result.Pod != "" || got[0].result.Validate() != nil {
				t.Errorf("received %+v, want a valid Error result with the notes %v and no Pod", got, tc.notes)
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
		{"drops a result for a branch that's gone", []int{410}, 1, ""},
		{"stops on a 404, which doesn't say that the branch is gone", []int{404}, 1, "Not Found"},
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
	for code, msg := range map[int]string{
		http.StatusBadRequest: "the core program rejected the lint check's result",
		http.StatusForbidden:  "the core program doesn't accept the lint check's results from this service account",
	} {
		f := newSendFixture(t, &endpoint{codes: []int{code}})
		f.verdict = Pass("clean")
		if err := f.runAndSend(f.context(t)); !kube.IsPermanent(err) || !strings.Contains(err.Error(), msg) {
			t.Errorf("after %d, err = %v, want a permanent error that says %q, because sending the same result again won't help", code, err, msg)
		}
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
	f.s.cfg = &Config{CoreURL: "http://127.0.0.1:1"}
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
	if truncateValues(nil, gitk8s.MaxOutputValueLength) != nil {
		t.Error("truncateValues(nil) isn't nil")
	}
	if got := truncateValues(map[string]string{"files": strings.Repeat("a.go ", 300)}, gitk8s.MaxOutputValueLength); len(got["files"]) != gitk8s.MaxOutputValueLength {
		t.Errorf("output of %d bytes, want %d", len(got["files"]), gitk8s.MaxOutputValueLength)
	}
}
