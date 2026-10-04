package main

import (
	"bytes"
	"cmp"
	"context"
	"crypto/sha256"
	"crypto/tls"
	"crypto/x509"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net"
	"net/http"
	"os"
	"slices"
	"strings"
	"sync"
	"time"
)

// reviewer checks service account tokens.
type reviewer interface {
	// review returns the namespace of the service account that token
	// belongs to, if the token is valid and has audience, or an error that
	// wraps errDenied if it isn't.
	review(ctx context.Context, token, audience string) (namespace string, err error)
}

var errDenied = errors.New("token denied")

// tokenReviewer asks the API server about tokens with TokenReviews, and
// remembers the answers for a while, so a build that reads hundreds of
// outputs makes one review.
type tokenReviewer struct {
	url       string
	tokenFile string
	client    *http.Client

	mu    sync.Mutex
	cache map[[sha256.Size]byte]review
}

type review struct {
	namespace string
	err       error
	expires   time.Time
}

const serviceAccountDir = "/var/run/secrets/kubernetes.io/serviceaccount"

// inCluster returns a tokenReviewer that uses the Pod's service account.
func inCluster() (*tokenReviewer, error) {
	host, port := os.Getenv("KUBERNETES_SERVICE_HOST"), os.Getenv("KUBERNETES_SERVICE_PORT")
	if host == "" || port == "" {
		return nil, errors.New("KUBERNETES_SERVICE_HOST and KUBERNETES_SERVICE_PORT aren't set")
	}
	ca, err := os.ReadFile(serviceAccountDir + "/ca.crt")
	if err != nil {
		return nil, err
	}
	pool := x509.NewCertPool()
	if !pool.AppendCertsFromPEM(ca) {
		return nil, errors.New("no certificates in " + serviceAccountDir + "/ca.crt")
	}
	return newTokenReviewer("https://"+net.JoinHostPort(host, port), serviceAccountDir+"/token", &http.Client{
		Timeout:   10 * time.Second,
		Transport: &http.Transport{TLSClientConfig: &tls.Config{RootCAs: pool}},
	}), nil
}

func newTokenReviewer(server, tokenFile string, client *http.Client) *tokenReviewer {
	return &tokenReviewer{
		url:       server + "/apis/authentication.k8s.io/v1/tokenreviews",
		tokenFile: tokenFile,
		client:    client,
		cache:     map[[sha256.Size]byte]review{},
	}
}

func (t *tokenReviewer) review(ctx context.Context, token, audience string) (string, error) {
	key := sha256.Sum256([]byte(audience + "\x00" + token))
	t.mu.Lock()
	r, ok := t.cache[key]
	t.mu.Unlock()
	if ok && time.Now().Before(r.expires) {
		return r.namespace, r.err
	}
	ns, err := t.ask(ctx, token, audience)
	ttl := time.Minute
	switch {
	case errors.Is(err, errDenied):
		ttl = 10 * time.Second
	case err != nil:
		return "", err
	}
	t.mu.Lock()
	if len(t.cache) >= 4096 {
		clear(t.cache)
	}
	t.cache[key] = review{namespace: ns, err: err, expires: time.Now().Add(ttl)}
	t.mu.Unlock()
	return ns, err
}

// tokenReview holds the fields of a TokenReview that go-cache uses.
type tokenReview struct {
	APIVersion string `json:"apiVersion"`
	Kind       string `json:"kind"`
	Spec       struct {
		Token     string   `json:"token"`
		Audiences []string `json:"audiences"`
	} `json:"spec"`
	Status struct {
		Authenticated bool `json:"authenticated"`
		User          struct {
			Username string `json:"username"`
		} `json:"user"`
		Audiences []string `json:"audiences"`
		Error     string   `json:"error"`
	} `json:"status"`
}

func (t *tokenReviewer) ask(ctx context.Context, token, audience string) (string, error) {
	tr := tokenReview{APIVersion: "authentication.k8s.io/v1", Kind: "TokenReview"}
	tr.Spec.Token = token
	tr.Spec.Audiences = []string{audience}
	body, err := json.Marshal(tr)
	if err != nil {
		return "", err
	}
	own, err := os.ReadFile(t.tokenFile)
	if err != nil {
		return "", err
	}
	req, err := http.NewRequestWithContext(ctx, http.MethodPost, t.url, bytes.NewReader(body))
	if err != nil {
		return "", err
	}
	req.Header.Set("Authorization", "Bearer "+strings.TrimSpace(string(own)))
	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("Accept", "application/json")
	resp, err := t.client.Do(req)
	if err != nil {
		return "", err
	}
	defer resp.Body.Close()
	b, err := io.ReadAll(io.LimitReader(resp.Body, 1<<20))
	if err != nil {
		return "", err
	}
	if resp.StatusCode != http.StatusCreated && resp.StatusCode != http.StatusOK {
		return "", fmt.Errorf("creating a TokenReview: %s: %s", resp.Status, bytes.TrimSpace(b))
	}
	var got tokenReview
	if err := json.Unmarshal(b, &got); err != nil {
		return "", fmt.Errorf("reading a TokenReview: %w", err)
	}
	return checkReview(&got, audience)
}

// checkReview returns the namespace of the service account that a
// TokenReview authenticated for audience. An API server that ignores the
// requested audiences returns none, so a token for any audience passes
// it; checkReview denies those.
func checkReview(tr *tokenReview, audience string) (string, error) {
	s := &tr.Status
	switch {
	case !s.Authenticated:
		return "", fmt.Errorf("%w: %s", errDenied, cmp.Or(s.Error, "not authenticated"))
	case !slices.Contains(s.Audiences, audience):
		return "", fmt.Errorf("%w: the token isn't for %s", errDenied, audience)
	}
	rest, ok := strings.CutPrefix(s.User.Username, "system:serviceaccount:")
	ns, name, _ := strings.Cut(rest, ":")
	if !ok || ns == "" || name == "" {
		return "", fmt.Errorf("%w: %s isn't a service account", errDenied, s.User.Username)
	}
	return ns, nil
}
