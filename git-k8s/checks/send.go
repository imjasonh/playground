package checks

import (
	"bytes"
	"cmp"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"log/slog"
	"net/http"
	"net/url"
	"strings"
	"sync"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/kube"
)

// defaultResultsURL is the results endpoint of the core program, as
// generate installs it.
const defaultResultsURL = "http://git-k8s.git-k8s.svc/results"

// sendAttempts is how many times a check tries to send a result before its
// reconcile fails and kube retries it, which runs the check again. A try
// fails while the core program restarts, and gets 503 while the core
// program can't write the result.
const sendAttempts = 10

// branch is the part of a GitBranch that a check controller reconciles. It
// declares no status, so kube writes none, and generate doesn't let the
// check write status.
type branch struct {
	kube.Object `kube:"apiVersion=git-k8s.imjasonh.com/v1alpha1,kind=GitBranch,plural=gitbranches,scope=Namespaced"`
	Spec        gitk8s.GitBranchSpec `json:"spec"`
}

type reconcileFunc func(context.Context, *branch) error

func (f reconcileFunc) Reconcile(ctx context.Context, b *branch) error { return f(ctx, b) }

// runAndSend runs r on the check's view of b, which holds the check's last
// result, and sends the new result to the core program if it's different.
func runAndSend[V any, P interface {
	kube.Resource[V]
	View
}](ctx context.Context, r kube.Reconciler[V], s *sender, b *branch) error {
	obj := kube.Get[V, P](ctx, b.Namespace, b.Name)
	if obj == nil {
		return nil
	}
	meta, _, result := P(obj).Parts()
	prev := *result
	err := r.Reconcile(ctx, obj)
	if res := *result; res != nil && !res.Equal(prev) {
		sendErr := s.send(ctx, meta, res)
		if errors.Is(sendErr, errGone) {
			// Running the check again can't help a branch that's gone.
			return nil
		}
		err = errors.Join(err, sendErr)
	}
	return err
}

// errGone is what send returns when the core program answers that the
// GitBranch is gone.
var errGone = errors.New("the GitBranch is gone")

// sender sends a check's results to the core program's results endpoint,
// with a token for the check's service account.
type sender struct {
	check  string
	cfg    *Config
	client *http.Client
	// delay is the wait before the second try, which doubles for each
	// later try, up to 2 seconds.
	delay time.Duration

	mu      sync.Mutex
	token   string
	expires time.Time
}

// send sets res as the check's result on the GitBranch that meta describes.
// The core program answers 503 and closes the connection while it can't
// write the result, as when its Pod starts or stops, so send tries again on
// a new connection, which can reach the Pod that replaces a stopping one.
// If the GitBranch is gone, send returns errGone.
func (s *sender) send(ctx context.Context, meta *kube.ObjectMeta, res *gitk8s.CheckResult) error {
	body, err := json.Marshal(res)
	if err != nil {
		return err
	}
	u := fmt.Sprintf("%s/%s/%s/%s?generation=%d", strings.TrimSuffix(cmp.Or(s.cfg.ResultsURL, defaultResultsURL), "/"),
		url.PathEscape(meta.Namespace), url.PathEscape(meta.Name), url.PathEscape(s.check), meta.Generation)
	delay := s.delay
	for attempt := 1; ; attempt++ {
		code, msg, err := s.put(ctx, u, body)
		switch {
		case err == nil && code == http.StatusNoContent:
			return nil
		case err == nil && code == http.StatusConflict:
			// The branch changed since the check read it, or its policy no
			// longer lists the check. Either way, the change runs the
			// check again.
			slog.Info("the core program didn't take a result", "check", s.check, "namespace", meta.Namespace, "branch", meta.Name, "reason", msg)
			return nil
		case err == nil && code == http.StatusNotFound:
			// The core program answers 404 only once the API server shows
			// that the GitBranch is gone.
			slog.Info("the core program didn't take a result", "check", s.check, "namespace", meta.Namespace, "branch", meta.Name, "reason", msg)
			return errGone
		case err == nil && code == http.StatusBadRequest:
			return kube.Permanent(fmt.Errorf("the core program rejected the %s check's result: %s", s.check, msg))
		case err == nil && code == http.StatusForbidden:
			return kube.Permanent(fmt.Errorf("the core program doesn't accept the %s check's results from this service account: %s", s.check, msg))
		case err == nil && code != http.StatusServiceUnavailable:
			return fmt.Errorf("sending the %s check's result to the core program: %s: %s", s.check, http.StatusText(code), msg)
		case err == nil:
			err = fmt.Errorf("the core program didn't write the %s check's result: %s", s.check, msg)
		}
		if attempt == sendAttempts {
			return err
		}
		select {
		case <-ctx.Done():
			return err
		case <-time.After(delay):
		}
		delay = min(2*delay, 2*time.Second)
	}
}

// put sends one request, and returns the response's status code and body.
func (s *sender) put(ctx context.Context, u string, body []byte) (int, string, error) {
	token, err := s.tokenFor(ctx)
	if err != nil {
		return 0, "", err
	}
	req, err := http.NewRequestWithContext(ctx, http.MethodPut, u, bytes.NewReader(body))
	if err != nil {
		return 0, "", err
	}
	req.Header.Set("Authorization", "Bearer "+token)
	req.Header.Set("Content-Type", "application/json")
	resp, err := s.client.Do(req)
	if err != nil {
		return 0, "", err
	}
	defer resp.Body.Close()
	if resp.StatusCode == http.StatusUnauthorized {
		s.forget(token)
	}
	msg, _ := io.ReadAll(io.LimitReader(resp.Body, 1024))
	return resp.StatusCode, strings.TrimSpace(string(msg)), nil
}

// tokenFor returns a token for the check's service account, reusing one
// until 10 minutes before it expires.
func (s *sender) tokenFor(ctx context.Context) (string, error) {
	s.mu.Lock()
	defer s.mu.Unlock()
	if s.token != "" && time.Until(s.expires) > 10*time.Minute {
		return s.token, nil
	}
	token, expires, err := kube.RequestToken(ctx, gitk8s.ResultsAudience)
	if err != nil {
		return "", err
	}
	s.token, s.expires = token, expires
	return token, nil
}

// forget stops reusing a token that the core program refused.
func (s *sender) forget(token string) {
	s.mu.Lock()
	defer s.mu.Unlock()
	if s.token == token {
		s.token = ""
	}
}
