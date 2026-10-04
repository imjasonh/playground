package main

import (
	"bytes"
	"cmp"
	"container/list"
	"context"
	"crypto/sha256"
	"crypto/tls"
	"crypto/x509"
	"encoding/base64"
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

	"golang.org/x/sync/singleflight"
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
// outputs makes one review. It denies a token that isn't a JWT for the
// audience without asking. It remembers denials apart from the tokens that
// it accepts, so bad tokens can't push good ones out, and it sends at most
// maxReviews TokenReviews at once.
type tokenReviewer struct {
	url       string
	tokenFile string
	client    *http.Client

	allowed, denied *reviewCache
	// reviews holds the reviews in progress, by key.
	reviews singleflight.Group
	// asking holds a value for each TokenReview in progress, up to its
	// capacity.
	asking chan struct{}
	// askWait is how long a review waits for others to finish.
	askWait time.Duration
}

const (
	// maxReviews is how many TokenReviews a tokenReviewer sends at once.
	maxReviews = 8
	// maxTokenSize is the size of the largest token that go-cache reviews.
	// Service account tokens take about a kilobyte.
	maxTokenSize = 16 << 10
)

type review struct {
	namespace string
	err       error
	expires   time.Time
}

// reviewCache remembers reviews for ttl. When it holds size reviews, it
// forgets the expired ones, or if none have expired, the least recently
// used one.
type reviewCache struct {
	size int
	ttl  time.Duration

	mu      sync.Mutex
	entries map[[sha256.Size]byte]*list.Element
	// lru holds a *cachedReview for each entry, the most recently used
	// first.
	lru list.List
}

type cachedReview struct {
	key [sha256.Size]byte
	review
}

func newReviewCache(size int, ttl time.Duration) *reviewCache {
	return &reviewCache{size: size, ttl: ttl, entries: map[[sha256.Size]byte]*list.Element{}}
}

// get returns the review for key, if c has one that hasn't expired by now.
func (c *reviewCache) get(key [sha256.Size]byte, now time.Time) (review, bool) {
	c.mu.Lock()
	defer c.mu.Unlock()
	e, ok := c.entries[key]
	if !ok {
		return review{}, false
	}
	r := e.Value.(*cachedReview)
	if !now.Before(r.expires) {
		c.remove(e)
		return review{}, false
	}
	c.lru.MoveToFront(e)
	return r.review, true
}

// add remembers r for key, until ttl after now.
func (c *reviewCache) add(key [sha256.Size]byte, r review, now time.Time) {
	r.expires = now.Add(c.ttl)
	c.mu.Lock()
	defer c.mu.Unlock()
	if e, ok := c.entries[key]; ok {
		e.Value.(*cachedReview).review = r
		c.lru.MoveToFront(e)
		return
	}
	if c.lru.Len() >= c.size {
		for e := c.lru.Front(); e != nil; {
			next := e.Next()
			if !now.Before(e.Value.(*cachedReview).expires) {
				c.remove(e)
			}
			e = next
		}
	}
	for c.lru.Len() >= c.size {
		c.remove(c.lru.Back())
	}
	c.entries[key] = c.lru.PushFront(&cachedReview{key, r})
}

func (c *reviewCache) remove(e *list.Element) {
	delete(c.entries, e.Value.(*cachedReview).key)
	c.lru.Remove(e)
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
		allowed:   newReviewCache(4096, time.Minute),
		denied:    newReviewCache(1024, 10*time.Second),
		asking:    make(chan struct{}, maxReviews),
		askWait:   10 * time.Second,
	}
}

func (t *tokenReviewer) review(ctx context.Context, token, audience string) (string, error) {
	if !forAudience(token, audience) {
		return "", fmt.Errorf("%w: the token isn't a JWT for %s", errDenied, audience)
	}
	key := sha256.Sum256([]byte(audience + "\x00" + token))
	if r, ok := t.remembered(key); ok {
		return r.namespace, r.err
	}
	// Reviews of one token share one TokenReview, which goes on if the
	// request that started it ends.
	v, err, _ := t.reviews.Do(string(key[:]), func() (any, error) {
		if r, ok := t.remembered(key); ok {
			return r, nil
		}
		ns, err := t.askSoon(context.WithoutCancel(ctx), token, audience)
		r := review{namespace: ns, err: err}
		switch {
		case errors.Is(err, errDenied):
			t.denied.add(key, r, time.Now())
		case err != nil:
			return nil, err
		default:
			t.allowed.add(key, r, time.Now())
		}
		return r, nil
	})
	if err != nil {
		return "", err
	}
	r := v.(review)
	return r.namespace, r.err
}

func (t *tokenReviewer) remembered(key [sha256.Size]byte) (review, bool) {
	now := time.Now()
	if r, ok := t.allowed.get(key, now); ok {
		return r, true
	}
	return t.denied.get(key, now)
}

// askSoon asks the API server about token once fewer than maxReviews
// TokenReviews are in progress, and fails if that takes longer than
// askWait.
func (t *tokenReviewer) askSoon(ctx context.Context, token, audience string) (string, error) {
	wait := time.NewTimer(t.askWait)
	defer wait.Stop()
	select {
	case t.asking <- struct{}{}:
	case <-wait.C:
		return "", errors.New("too many token reviews are in progress")
	case <-ctx.Done():
		return "", ctx.Err()
	}
	defer func() { <-t.asking }()
	return t.ask(ctx, token, audience)
}

// forAudience reports whether token is a JWT whose aud claim includes
// audience. It doesn't check the token's signature, so only the API server
// can accept a token, but it spares the API server tokens that it would
// deny.
func forAudience(token, audience string) bool {
	if len(token) > maxTokenSize {
		return false
	}
	parts := strings.Split(token, ".")
	if len(parts) != 3 || parts[0] == "" || parts[2] == "" {
		return false
	}
	payload, err := base64.RawURLEncoding.DecodeString(parts[1])
	if err != nil {
		return false
	}
	var claims struct {
		Aud json.RawMessage `json:"aud"`
	}
	if json.Unmarshal(payload, &claims) != nil {
		return false
	}
	// aud is a string or a list of strings.
	var auds []string
	if json.Unmarshal(claims.Aud, &auds) != nil {
		var aud string
		if json.Unmarshal(claims.Aud, &aud) != nil {
			return false
		}
		auds = []string{aud}
	}
	return slices.Contains(auds, audience)
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
