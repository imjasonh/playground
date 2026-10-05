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
	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
)

// maxResultSize bounds the body of a request to the results endpoint.
const maxResultSize = 256 << 10

// The admission policies in config/policy.yaml read the same ConfigMap, and
// name the same service account as the core program's.
const (
	checksNamespace = "git-k8s"
	checksConfigMap = "git-k8s-checks"
	coreAccount     = "git-k8s.git-k8s"
)

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
	cm, err := kube.Fetch[k8s.ConfigMap](r.Context(), checksNamespace, checksConfigMap)
	if err != nil {
		slog.ErrorContext(r.Context(), "reading the git-k8s-checks ConfigMap failed", "err", err)
		http.Error(w, "can't read the git-k8s-checks ConfigMap now", http.StatusInternalServerError)
		return
	}
	var entries map[string]string
	if cm != nil {
		entries = cm.Data
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
// shows it in the branch's status. It answers 503 if that takes too long,
// or 404 if the cache doesn't have the branch by then.
func (rs *results) write(w http.ResponseWriter, r *http.Request, k kube.Key, check string, res *gitk8s.CheckResult, generation int64) {
	ctx := r.Context()
	timeout := time.NewTimer(rs.timeout)
	defer timeout.Stop()
	poll := time.NewTicker(rs.poll)
	defer poll.Stop()
	held := false
	defer func() {
		if held {
			rs.release(k, check, res)
		}
	}()
	for {
		b := kube.Get[resultsBranch](ctx, k.Namespace, k.Name)
		if b == nil && ctx.Err() != nil {
			// A Get that can't read cancels the request's context.
			unavailable(w, "can't read the branch now")
			return
		}
		// Until this replica's cache has the branch at the generation that
		// the check read, the branch can look missing or the result stale.
		if b != nil && b.Generation >= generation {
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
		}
		select {
		case <-ctx.Done():
			return
		case <-timeout.C:
			if b == nil {
				http.Error(w, fmt.Sprintf("GitBranch %s doesn't exist", k), http.StatusNotFound)
				return
			}
			unavailable(w, "the result wasn't written in time")
			return
		case <-poll.C:
		}
	}
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

// checkFor returns the name of the check that runs as user. Each of entries,
// the data of the git-k8s-checks ConfigMap, maps NAMESPACE.SERVICE_ACCOUNT
// to a check's name, or to "" for a service account that isn't a check.
// Without an entry, generate's convention applies: it installs each program
// in a namespace with a service account of the program's name, so the gofmt
// check runs as the service account check-gofmt in the namespace
// check-gofmt. The core program's service account is never a check. The
// check variable of the policies in config/policy.yaml maps service
// accounts the same way, so change both together.
func checkFor(user kube.UserInfo, entries map[string]string) (string, bool) {
	ns, name, ok := user.ServiceAccount()
	if !ok || ns+"."+name == coreAccount {
		return "", false
	}
	if check, ok := entries[ns+"."+name]; ok {
		return check, check != ""
	}
	check, isCheck := strings.CutPrefix(name, "check-")
	if !isCheck || ns != name || check == "" {
		return "", false
	}
	return check, true
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
