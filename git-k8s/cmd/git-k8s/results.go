package main

import (
	"context"
	"encoding/json"
	"fmt"
	"io"
	"log/slog"
	"maps"
	"net/http"
	"strconv"
	"strings"
	"sync"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/caller"
	"github.com/imjasonh/playground/kube"
)

// maxResultSize bounds the body of a request to the results endpoint.
const maxResultSize = 256 << 10

// resultsBranch is the part of a GitBranch that the results controller
// writes. status.checks is an atomic map, so each write replaces all of its
// entries, and this controller is the only manager of any of them.
type resultsBranch struct {
	kube.Object `kube:"apiVersion=git-k8s.imjasonh.com/v1alpha1,kind=GitBranch,plural=gitbranches,scope=Namespaced"`
	Spec        gitk8s.GitBranchSpec `json:"spec"`
	Status      struct {
		Checks map[string]gitk8s.CheckResult `json:"checks"`
	} `json:"status,omitzero"`
}

// results is the results endpoint, which checks send their results to, and
// the controller that writes the results to status.checks. A check proves
// which check it is with a token for its service account, so it can write
// only its own entry.
//
// A handler can't write, so it holds each result for the controller,
// triggers a reconcile of the branch, and answers once the cache shows the
// result written. The controller leaves the results held, so that a retry
// of a failed write still has them, and each request stops holding its
// result when it answers.
type results struct {
	// timeout is how long a request waits for its result to be written.
	timeout time.Duration
	// poll is how often a waiting request looks for its result in the
	// cache.
	poll time.Duration
	// refetch is how often a request that doesn't find the branch in the
	// cache, at the generation that the check read, reads the branch from
	// the API server to learn whether it's gone. The first miss reads it at
	// once.
	refetch time.Duration
	// fetch is kube.Fetch, except in tests.
	fetch func(ctx context.Context, namespace, name string) (*resultsBranch, error)
	// checks holds the entries of the git-k8s-checks ConfigMap. Nil reads
	// the ConfigMap for every request.
	checks *caller.Checks

	mu   sync.Mutex
	held map[kube.Key]map[string]*gitk8s.CheckResult
}

func (rs *results) handler() http.Handler {
	mux := http.NewServeMux()
	mux.HandleFunc("PUT /results/{namespace}/{name}/{check}", rs.put)
	return mux
}

// put sets one check's result on a GitBranch. The request's generation is
// the GitBranch's generation that the check read.
func (rs *results) put(w http.ResponseWriter, r *http.Request) {
	scheme, token, _ := strings.Cut(r.Header.Get("Authorization"), " ")
	if !strings.EqualFold(scheme, "Bearer") {
		w.Header().Set("WWW-Authenticate", "Bearer")
		http.Error(w, "the request has no Bearer token", http.StatusUnauthorized)
		return
	}
	review, err := kube.ReviewToken(r.Context(), strings.TrimLeft(token, " "), gitk8s.ResultsAudience)
	switch {
	case err != nil:
		// The error can name the core program's service account and the
		// permission that it lacks.
		slog.ErrorContext(r.Context(), "reviewing a check's token failed", "err", err)
		http.Error(w, "can't check the token now", http.StatusInternalServerError)
		return
	case !review.Authenticated:
		w.Header().Set("WWW-Authenticate", "Bearer")
		http.Error(w, review.Error, http.StatusUnauthorized)
		return
	}
	entries, err := rs.checks.Entries(r.Context())
	if err != nil {
		slog.ErrorContext(r.Context(), "reading the git-k8s-checks ConfigMap failed", "err", err)
		http.Error(w, "can't read the git-k8s-checks ConfigMap now", http.StatusInternalServerError)
		return
	}
	entry := r.PathValue("check")
	check, ok := checkFor(review.User, entries)
	switch {
	case !ok:
		http.Error(w, review.User.Username+" isn't a check's service account", http.StatusForbidden)
		return
	case check != entry:
		http.Error(w, fmt.Sprintf("%s is the %s check, so it can't write the %s check's result", review.User.Username, check, entry), http.StatusForbidden)
		return
	}

	var res gitk8s.CheckResult
	dec := json.NewDecoder(http.MaxBytesReader(w, r.Body, maxResultSize))
	if err := dec.Decode(&res); err != nil {
		http.Error(w, "decoding the result: "+err.Error(), http.StatusBadRequest)
		return
	}
	if _, err := dec.Token(); err != io.EOF {
		http.Error(w, "the request has data after the result", http.StatusBadRequest)
		return
	}
	if err := res.Validate(); err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}
	var generation int64
	if g := r.URL.Query().Get("generation"); g != "" {
		if generation, err = strconv.ParseInt(g, 10, 64); err != nil {
			http.Error(w, "generation: "+err.Error(), http.StatusBadRequest)
			return
		}
	}
	rs.write(w, r, kube.Key{Namespace: r.PathValue("namespace"), Name: r.PathValue("name")}, check, &res, generation)
}

// write holds res for the results controller and answers once the cache
// shows it in the branch's status. It answers 503 if that takes too long.
//
// Until this replica's cache has the branch at the generation that the
// check read, the branch can look missing or the result stale, because the
// check's cache can get a change first. So until then, write also reads the
// branch from the API server, and answers as soon as that shows the branch
// gone.
func (rs *results) write(w http.ResponseWriter, r *http.Request, k kube.Key, check string, res *gitk8s.CheckResult, generation int64) {
	ctx := r.Context()
	timeout := time.NewTimer(rs.timeout)
	defer timeout.Stop()
	// A read from the API server ends when the request stops waiting.
	fetchCtx, cancel := context.WithTimeout(ctx, rs.timeout)
	defer cancel()
	poll := time.NewTicker(rs.poll)
	defer poll.Stop()
	held := false
	defer func() {
		if held {
			rs.release(k, check, res)
		}
	}()
	var fetched time.Time
	for {
		b := kube.Get[resultsBranch](ctx, k.Namespace, k.Name)
		if b == nil && ctx.Err() != nil {
			// A Get that can't read cancels the request's context.
			unavailable(w, "can't read the branch now")
			return
		}
		switch {
		case b != nil && b.Generation >= generation:
			if reason := rejection(&b.Spec, check, res); reason != "" {
				http.Error(w, reason, http.StatusConflict)
				return
			}
			if cur, ok := b.Status.Checks[check]; ok && res.Equal(&cur) {
				w.WriteHeader(http.StatusNoContent)
				return
			}
			if !held {
				rs.hold(k, check, res)
				held = true
				if !kube.Trigger[resultsBranch](ctx, k.Namespace, k.Name) {
					unavailable(w, "this replica doesn't write the branch's results")
					return
				}
			}
		case time.Since(fetched) >= rs.refetch:
			fetched = time.Now()
			if code, msg := rs.gone(fetchCtx, k, generation); code != 0 {
				http.Error(w, msg, code)
				return
			}
		}
		select {
		case <-ctx.Done():
			return
		case <-timeout.C:
			unavailable(w, "the result wasn't written in time")
			return
		case <-poll.C:
		}
	}
}

// gone reads the branch from the API server. If the GitBranch that the
// check read at generation is gone, it returns the status and the message
// to answer with. Otherwise it returns 0, and the request keeps waiting for
// the cache, as it does when the read fails.
func (rs *results) gone(ctx context.Context, k kube.Key, generation int64) (int, string) {
	fetch := kube.Fetch[resultsBranch]
	if rs.fetch != nil {
		fetch = rs.fetch
	}
	b, err := fetch(ctx, k.Namespace, k.Name)
	switch {
	case err != nil:
		slog.WarnContext(ctx, "reading a GitBranch for a check's result failed", "namespace", k.Namespace, "branch", k.Name, "err", err)
		return 0, ""
	case b == nil:
		return http.StatusGone, fmt.Sprintf("GitBranch %s doesn't exist", k)
	case b.Generation < generation:
		// A GitBranch's generation never decreases, so this one is another
		// GitBranch with the same name, which the check runs on again.
		return http.StatusConflict, fmt.Sprintf("the check read generation %d of GitBranch %s, which is at generation %d, so it was deleted and created again", generation, k, b.Generation)
	}
	return 0, ""
}

// unavailable answers 503 and closes the connection, so that the client's
// next try can reach the replica that writes the branch's results.
func unavailable(w http.ResponseWriter, msg string) {
	w.Header().Set("Connection", "close")
	http.Error(w, msg+"; try again", http.StatusServiceUnavailable)
}

func (rs *results) hold(k kube.Key, check string, res *gitk8s.CheckResult) {
	rs.mu.Lock()
	defer rs.mu.Unlock()
	if rs.held == nil {
		rs.held = map[kube.Key]map[string]*gitk8s.CheckResult{}
	}
	if rs.held[k] == nil {
		rs.held[k] = map[string]*gitk8s.CheckResult{}
	}
	rs.held[k][check] = res
}

// release stops holding res, unless a later request replaced it.
func (rs *results) release(k kube.Key, check string, res *gitk8s.CheckResult) {
	rs.mu.Lock()
	defer rs.mu.Unlock()
	if rs.held[k][check] != res {
		return
	}
	delete(rs.held[k], check)
	if len(rs.held[k]) == 0 {
		delete(rs.held, k)
	}
}

func (rs *results) heldFor(k kube.Key) map[string]*gitk8s.CheckResult {
	rs.mu.Lock()
	defer rs.mu.Unlock()
	return maps.Clone(rs.held[k])
}

// Reconcile writes the results that requests hold for b, and removes the
// results of checks that b's merge policy doesn't list.
func (rs *results) Reconcile(ctx context.Context, b *resultsBranch) error {
	held := rs.heldFor(kube.Key{Namespace: b.Namespace, Name: b.Name})
	// A request stops holding its result once the cache shows it written,
	// which can be after kube read b from the cache. Reading the branch
	// after taking the held results sees every result that a request
	// stopped holding.
	cur := kube.Get[resultsBranch](ctx, b.Namespace, b.Name)
	if cur == nil {
		return nil
	}
	checks := map[string]gitk8s.CheckResult{}
	for name, r := range cur.Status.Checks {
		if listed(&cur.Spec, name) {
			checks[name] = r
		}
	}
	for name, r := range held {
		if rejection(&cur.Spec, name, r) == "" {
			checks[name] = *r
		}
	}
	// An empty map, rather than none, removes the last entry.
	if len(checks) > 0 || len(cur.Status.Checks) > 0 {
		b.Status.Checks = checks
	}
	return nil
}

// checkFor returns the name of the check that runs as user, which must be a
// service account. The mirror maps service accounts to checks the same way,
// with entries from the git-k8s-checks ConfigMap, as caller.Caller.Check
// describes.
func checkFor(user kube.UserInfo, entries map[string]string) (string, bool) {
	ns, name, ok := user.ServiceAccount()
	if !ok {
		return "", false
	}
	return caller.Caller{Namespace: ns, Name: name}.Check(entries)
}

// listed reports whether spec's merge policy lists the check, so that a
// result for it belongs in status.checks.
func listed(spec *gitk8s.GitBranchSpec, check string) bool {
	return spec.Parent != "" && spec.Merge.Check(check) != nil
}

// rejection returns why a branch with spec can't take r as the check's
// result, or "" if it can.
func rejection(spec *gitk8s.GitBranchSpec, check string, r *gitk8s.CheckResult) string {
	switch {
	case spec.Parent == "":
		return fmt.Sprintf("%s has no parent, so it takes no check results", spec.Branch)
	case !listed(spec, check):
		return fmt.Sprintf("the merge policy for %s doesn't list the %s check", spec.Branch, check)
	case !r.Fresh(spec.Head, spec.ParentHead):
		return fmt.Sprintf("the result isn't for %s at %s and %s at %s", spec.Branch, gitk8s.Short(spec.Head), spec.Parent, gitk8s.Short(spec.ParentHead))
	}
	return ""
}
