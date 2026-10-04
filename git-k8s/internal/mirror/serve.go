package mirror

import (
	"bytes"
	"cmp"
	"compress/gzip"
	"errors"
	"fmt"
	"io"
	"log/slog"
	"net/http"
	"regexp"
	"strings"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/caller"
	"github.com/imjasonh/playground/kube"
)

var pathRE = regexp.MustCompile(`^/([a-z0-9]([-a-z0-9]*[a-z0-9])?)/([a-z0-9]([-a-z0-9.]*[a-z0-9])?)\.git/(info/refs|git-upload-pack|git-receive-pack)$`)

// ServeHTTP serves each copy over git's smart HTTP protocol at
// gitk8s.MirrorPath. Every request needs a service account token whose
// audience is gitk8s.MirrorAudience as a bearer token. Run it with
// kube.Serve: it reads GitRepository and GitBranch objects, checks tokens
// with kube.ReviewToken, gets the Pod that a test Pod's token is bound to
// with kube.Fetch, and calls kube.Trigger for a GitRepository after a push.
func (m *Mirror) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	// A request may take this long to arrive, and its response as long
	// again. Without a write deadline, a client that stops reading blocks
	// the goroutine that copies git's output even after git stops, and the
	// handler holds the copy open until the client disconnects.
	limit := cmp.Or(m.readTimeout, m.Git.MaxDuration())
	rc := http.NewResponseController(w)
	_ = rc.SetWriteDeadline(time.Now().Add(2 * limit))
	match := pathRE.FindStringSubmatch(r.URL.Path)
	if match == nil {
		http.NotFound(w, r)
		return
	}
	namespace, name, op := match[1], match[3], match[5]
	service := strings.TrimPrefix(op, "git-")
	switch {
	case op == "info/refs" && r.Method == http.MethodGet:
		service = strings.TrimPrefix(r.URL.Query().Get("service"), "git-")
		if service != "upload-pack" && service != "receive-pack" {
			http.Error(w, "the mirror serves only git's smart HTTP protocol", http.StatusForbidden)
			return
		}
	case op != "info/refs" && r.Method == http.MethodPost:
	default:
		http.Error(w, "method not allowed", http.StatusMethodNotAllowed)
		return
	}

	ctx := r.Context()
	who, err := caller.Identify(ctx, r, gitk8s.MirrorAudience)
	switch {
	case errors.Is(err, caller.ErrUnauthenticated):
		w.Header().Set("WWW-Authenticate", `Bearer realm="git-k8s"`)
		http.Error(w, err.Error(), http.StatusUnauthorized)
		return
	case err != nil:
		slog.Warn("checking a token failed", "err", err)
		http.Error(w, "the mirror couldn't check the token; try again", http.StatusServiceUnavailable)
		return
	}
	repo := kube.Get[gitk8s.Repository](ctx, namespace, name)
	may := false
	if repo != nil {
		if may, err = m.mayFetch(ctx, who, repo); err != nil {
			slog.Warn("checking a caller failed", "repository", namespace+"/"+name, "caller", who.String(), "err", err)
			http.Error(w, "the mirror couldn't check the caller; try again", http.StatusServiceUnavailable)
			return
		}
	}
	if !may {
		http.Error(w, fmt.Sprintf("no GitRepository %s/%s that %s may fetch", namespace, name, who), http.StatusNotFound)
		return
	}
	if service == "receive-pack" && !m.mayPushAny(who, repo) {
		http.Error(w, fmt.Sprintf("%s may not push to %s/%s", who, namespace, name), http.StatusForbidden)
		return
	}

	w.Header().Set("Cache-Control", "no-cache")
	body := io.Reader(r.Body)
	var p *pushRequest
	if op != "info/refs" {
		// git writes its response while it reads the request.
		_ = rc.EnableFullDuplex()
		_ = rc.SetReadDeadline(time.Now().Add(limit))
		if r.Header.Get("Content-Encoding") == "gzip" {
			zr, err := gzip.NewReader(r.Body)
			if err != nil {
				http.Error(w, err.Error(), http.StatusBadRequest)
				return
			}
			defer zr.Close()
			body = zr
		}
		if service == "receive-pack" {
			// While a copy is open, the mirror can't replace or delete it,
			// and once that waits, nothing else can open it. So the mirror
			// judges a push before it opens the copy, and a client that's
			// slow to send its updates, or that sends updates the mirror
			// refuses, doesn't hold the copy. A client that's slow to send
			// the pack after them holds it until the read deadline.
			var start bytes.Buffer
			if p, err = readPush(io.TeeReader(body, &start)); err != nil {
				http.Error(w, err.Error(), http.StatusBadRequest)
				return
			}
			if reasons := m.refusals(who, repo, p); reasons != nil {
				refuseAll(w, r, p, reasons)
				slog.Info("refused a push", "repository", namespace+"/"+name, "caller", who.String(), "refs", len(p.commands), "reason", reasons[0])
				return
			}
			body = io.MultiReader(&start, body)
		}
	}

	cp, err := m.Open(ctx, repo)
	switch {
	case errors.Is(err, ErrNotSynced):
		http.Error(w, err.Error(), http.StatusServiceUnavailable)
		return
	case err != nil:
		slog.Error("opening a copy failed", "repository", namespace+"/"+name, "err", err)
		http.Error(w, "the mirror couldn't open the repository", http.StatusInternalServerError)
		return
	}
	defer cp.Close()

	// Only fetches speak protocol version 2.
	protocol := ""
	if service == "upload-pack" && strings.Contains(r.Header.Get("Git-Protocol"), "version=2") {
		protocol = "version=2"
	}
	if op == "info/refs" {
		w.Header().Set("Content-Type", "application/x-git-"+service+"-advertisement")
		if protocol == "" {
			fmt.Fprintf(w, "%04x# service=git-%s\n0000", len(service)+19, service)
		}
		if err := m.Git.Advertise(ctx, service, cp.Dir, protocol, w); err != nil {
			slog.Warn("advertising refs failed", "repository", namespace+"/"+name, "err", err)
		}
		return
	}
	w.Header().Set("Content-Type", "application/x-git-"+service+"-result")
	if err := m.Git.Serve(ctx, service, cp.Dir, protocol, body, w); err != nil {
		slog.Warn("serving a request failed", "repository", namespace+"/"+name, "service", service, "err", err)
	}
	if p != nil && len(p.commands) > 0 {
		// git doesn't retry a push, so the mirror took it either way. If
		// this replica doesn't reconcile the repository now, the next poll
		// syncs the push.
		queued := kube.Trigger[gitk8s.GitRepository](ctx, namespace, name)
		slog.Info("served a push", "repository", namespace+"/"+name, "caller", who.String(), "refs", len(p.commands), "triggered", queued)
	}
}

// refusals returns why who may not make each update in p, or nil if it may
// make them all. The mirror refuses a push whole, so it either makes every
// update or none.
func (m *Mirror) refusals(who caller.Caller, repo *gitk8s.Repository, p *pushRequest) []string {
	reasons := make([]string, len(p.commands))
	refused := false
	for i, c := range p.commands {
		reasons[i] = m.refuse(who, repo, c)
		refused = refused || reasons[i] != ""
	}
	if !refused {
		return nil
	}
	for i := range reasons {
		if reasons[i] == "" {
			reasons[i] = "another update in the push was refused"
		}
	}
	return reasons
}

// refuseAll answers a push with a refusal of every update in it.
func refuseAll(w http.ResponseWriter, r *http.Request, p *pushRequest, reasons []string) {
	// The client reads the response only after it sends the whole pack. A
	// client that sends a bigger pack than a copy takes gets an error
	// instead of the reasons.
	_, _ = io.Copy(io.Discard, io.LimitReader(r.Body, maxPushSize))
	if !p.has("report-status") && !p.has("report-status-v2") {
		http.Error(w, strings.Join(reasons, "; "), http.StatusForbidden)
		return
	}
	w.Header().Set("Content-Type", "application/x-git-receive-pack-result")
	_, _ = w.Write(refusal(p, reasons))
}
