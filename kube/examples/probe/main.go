// Command probe checks URLs for Probe objects, and serves an HTTP API that
// other programs in the cluster call:
//
//	apiVersion: examples.kube.imjasonh.github.io/v1
//	kind: Probe
//	metadata:
//	  name: api
//	  namespace: team
//	spec:
//	  url: http://api.team.svc/healthz
//
// It shows how programs prove who they are to each other with service
// account tokens. Each check sends a token for the program's own service
// account, from RequestToken, with the audience "probe", so the URL's server
// must accept that audience. Every replica serves the API, which checks each
// caller's token with ReviewToken:
//
//   - GET /whoami answers with the caller's username.
//   - POST /probes/NAMESPACE/NAME checks a URL now, with Trigger. A service
//     account can run only the probes in its own namespace.
//
// A Probe of the program's own /whoami checks that the program can request
// a token and review it.
package main

import (
	"context"
	"flag"
	"fmt"
	"io"
	"log/slog"
	"net/http"
	"strings"
	"time"

	"github.com/imjasonh/playground/kube"
)

// Probe is a URL to check.
type Probe struct {
	kube.Object `kube:"group=examples.kube.imjasonh.github.io"`
	Spec        ProbeSpec   `json:"spec"`
	Status      ProbeStatus `json:"status,omitzero"`
}

// ProbeSpec is what to check.
type ProbeSpec struct {
	URL string `json:"url" kube:"minLength=1" doc:"URL to send a GET request to, with a token for the audience probe."`
}

// checkAudience is the audience of the tokens that checks send. The program
// chooses it, not a Probe. Whoever chooses both a check's URL and its
// audience can have the program send them a token for any server that
// trusts the cluster's tokens, such as the API server. Because it's a
// constant, the generate command mounts the token into the program's Pod
// instead of letting the program request tokens.
const checkAudience = "probe"

// ProbeStatus is the result of the last check.
type ProbeStatus struct {
	Code      int       `json:"code,omitempty" kube:"column=Code" doc:"HTTP status code of the response."`
	Message   string    `json:"message,omitempty" doc:"First line of the response, or why there's no response."`
	CheckedAt time.Time `json:"checkedAt,omitzero"`
}

type reconciler struct {
	client *http.Client
	// interval is how often to check each URL. It's a pointer so a flag can
	// set it after the controller is built.
	interval *time.Duration
}

func (r *reconciler) Reconcile(ctx context.Context, p *Probe) error {
	token, _, err := kube.RequestToken(ctx, checkAudience)
	if err != nil {
		p.Status.Code, p.Status.Message = 0, err.Error()
		return err
	}
	p.Status.Code, p.Status.Message = r.check(ctx, p.Spec.URL, token)
	p.Status.CheckedAt = time.Now()
	kube.RequeueAfter(ctx, *r.interval)
	return nil
}

// check sends a GET request for url with token, and returns the response's
// status code and first line.
func (r *reconciler) check(ctx context.Context, url, token string) (int, string) {
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, url, nil)
	if err != nil {
		return 0, err.Error()
	}
	req.Header.Set("Authorization", "Bearer "+token)
	resp, err := r.client.Do(req)
	if err != nil {
		return 0, err.Error()
	}
	defer resp.Body.Close()
	body, _ := io.ReadAll(io.LimitReader(resp.Body, 256))
	line, _, _ := strings.Cut(string(body), "\n")
	return resp.StatusCode, line
}

// api is the program's HTTP API.
type api struct {
	// audience is the audience that callers' tokens must have. It's a
	// pointer so a flag can set it after the handler is built.
	audience *string
}

func (a *api) handler() http.Handler {
	mux := http.NewServeMux()
	mux.HandleFunc("GET /whoami", a.whoami)
	mux.HandleFunc("POST /probes/{namespace}/{name}", a.run)
	return mux
}

// caller returns the user that the request's bearer token belongs to, or
// answers the request with an error.
func (a *api) caller(w http.ResponseWriter, r *http.Request) (kube.UserInfo, bool) {
	token, _ := strings.CutPrefix(r.Header.Get("Authorization"), "Bearer ")
	review, err := kube.ReviewToken(r.Context(), token, *a.audience)
	switch {
	case err != nil:
		// The error can name the program's service account and the
		// permission that it lacks.
		slog.ErrorContext(r.Context(), "reviewing a caller's token failed", "err", err)
		http.Error(w, "can't check the token now", http.StatusInternalServerError)
	case !review.Authenticated:
		w.Header().Set("WWW-Authenticate", "Bearer")
		http.Error(w, review.Error, http.StatusUnauthorized)
	default:
		return review.User, true
	}
	return kube.UserInfo{}, false
}

func (a *api) whoami(w http.ResponseWriter, r *http.Request) {
	user, ok := a.caller(w, r)
	if !ok {
		return
	}
	if pod := user.Extra["authentication.kubernetes.io/pod-name"]; len(pod) == 1 {
		fmt.Fprintf(w, "%s in Pod %s\n", user.Username, pod[0])
		return
	}
	fmt.Fprintln(w, user.Username)
}

func (a *api) run(w http.ResponseWriter, r *http.Request) {
	user, ok := a.caller(w, r)
	if !ok {
		return
	}
	ns, name := r.PathValue("namespace"), r.PathValue("name")
	if own, _, _ := user.ServiceAccount(); own != ns {
		http.Error(w, user.Username+" can't run probes in "+ns, http.StatusForbidden)
		return
	}
	if kube.Trigger[Probe](r.Context(), ns, name) {
		w.WriteHeader(http.StatusAccepted)
		return
	}
	if kube.Get[Probe](r.Context(), ns, name) == nil {
		http.NotFound(w, r)
		return
	}
	// The client's next try reaches another replica, which may hold the
	// probe's shard, only on a new connection.
	w.Header().Set("Connection", "close")
	http.Error(w, "this replica can't check the probe now; try again", http.StatusServiceUnavailable)
}

func main() {
	interval := flag.Duration("interval", 10*time.Minute, "how often to check each URL")
	audience := flag.String("audience", "probe", "audience that callers' tokens must have")
	kube.Main(
		kube.For[Probe](&reconciler{client: &http.Client{Timeout: 10 * time.Second}, interval: interval}),
		kube.Serve((&api{audience: audience}).handler()),
	)
}
