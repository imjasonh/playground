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
	"net/url"
	"os"
	"slices"
	"strings"
	"sync"
	"time"

	"golang.org/x/sync/singleflight"
)

// reviewer checks service account tokens, and the Pods that they're bound
// to.
type reviewer interface {
	// review returns who token belongs to, if the token is valid and has
	// audience, or an error that wraps errDenied if it isn't.
	review(ctx context.Context, token, audience string) (identity, error)
	// checkWriter returns nil if the token that id came from may write to
	// the build caches, or an error that wraps errDenied if it may not.
	checkWriter(ctx context.Context, id identity) error
}

// identity is who a token belongs to.
type identity struct {
	// namespace is the namespace of the token's service account.
	namespace string
	// pod and podUID name the Pod that the token is bound to, if any.
	pod, podUID string
}

var errDenied = errors.New("token denied")

const (
	// The kubelet binds each token that it projects to its Pod. A
	// TokenReview of a token that's bound to a Pod names the Pod with these
	// keys in user.extra.
	podNameExtra = "authentication.kubernetes.io/pod-name"
	podUIDExtra  = "authentication.kubernetes.io/pod-uid"
	// controllerLabel is the label that kube puts on each object that a
	// controller owns, with the controller's name.
	controllerLabel = "kube.imjasonh.github.io/controller"
)

// tokenReviewer asks the API server about tokens with TokenReviews, and
// remembers the answers for a while, so a build that reads hundreds of
// outputs makes one review. It denies a token that isn't a JWT for the
// audience without asking. It remembers denials apart from the tokens that
// it accepts, so bad tokens can't push good ones out, and it sends at most
// maxReviews TokenReviews at once.
//
// A token that writes must also be bound to a Pod that writer owns, and
// that hasn't finished. tokenReviewer gets the Pod for each write, at most
// maxPodGets at once, so writes stop once the Pod finishes.
type tokenReviewer struct {
	server    string
	tokenFile string
	client    *http.Client
	// writer is the name of the kube controller whose Pods may write.
	writer string

	allowed, denied *reviewCache
	// reviews holds the reviews in progress, by key.
	reviews singleflight.Group
	// asking holds a value for each TokenReview in progress, up to its
	// capacity.
	asking chan struct{}
	// pods holds the Pod checks in progress, by Pod.
	pods singleflight.Group
	// podsDenied remembers the Pods that failed a check. Only a Pod without
	// writer's label could pass a later check, and kube labels writer's
	// Pods when it creates them.
	podsDenied *reviewCache
	// getting holds a value for each Pod get in progress, up to its
	// capacity. Pod gets don't share slots with TokenReviews, so tokens that
	// fail their reviews can't hold up writes with tokens that passed
	// theirs. Tokens bound to Pods that fail the check can, but podsDenied
	// remembers each such Pod for 10 seconds, so each costs at most one get
	// every 10 seconds.
	getting chan struct{}
	// askWait is how long a request to the API server waits for others to
	// finish.
	askWait time.Duration
}

const (
	// maxReviews is how many TokenReviews a tokenReviewer sends at once.
	maxReviews = 8
	// maxPodGets is how many Pods a tokenReviewer gets at once.
	maxPodGets = 8
	// maxTokenSize is the size of the largest token that go-cache reviews.
	// Service account tokens take about a kilobyte.
	maxTokenSize = 16 << 10
)

type review struct {
	identity
	err     error
	expires time.Time
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

// inCluster returns a tokenReviewer that uses the Pod's service account,
// and lets the Pods of the kube controller named writer write.
func inCluster(writer string) (*tokenReviewer, error) {
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
		Timeout: 10 * time.Second,
		// A Transport with its own TLS config uses only HTTP/1.1 unless
		// ForceAttemptHTTP2 is set. Over HTTP/1.1 it keeps 2 idle
		// connections, so concurrent writes' Pod gets would keep opening
		// new ones.
		Transport: &http.Transport{TLSClientConfig: &tls.Config{RootCAs: pool}, ForceAttemptHTTP2: true},
	}, writer), nil
}

func newTokenReviewer(server, tokenFile string, client *http.Client, writer string) *tokenReviewer {
	return &tokenReviewer{
		server:     server,
		tokenFile:  tokenFile,
		client:     client,
		writer:     writer,
		allowed:    newReviewCache(4096, time.Minute),
		denied:     newReviewCache(1024, 10*time.Second),
		podsDenied: newReviewCache(1024, 10*time.Second),
		asking:     make(chan struct{}, maxReviews),
		getting:    make(chan struct{}, maxPodGets),
		askWait:    10 * time.Second,
	}
}

func (t *tokenReviewer) review(ctx context.Context, token, audience string) (identity, error) {
	if !forAudience(token, audience) {
		return identity{}, fmt.Errorf("%w: the token isn't a JWT for %s", errDenied, audience)
	}
	key := sha256.Sum256([]byte(audience + "\x00" + token))
	if r, ok := t.remembered(key); ok {
		return r.identity, r.err
	}
	// Reviews of one token share one TokenReview, which goes on if the
	// request that started it ends.
	v, err, _ := t.reviews.Do(string(key[:]), func() (any, error) {
		if r, ok := t.remembered(key); ok {
			return r, nil
		}
		id, err := t.askSoon(context.WithoutCancel(ctx), token, audience)
		r := review{identity: id, err: err}
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
		return identity{}, err
	}
	r := v.(review)
	return r.identity, r.err
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
func (t *tokenReviewer) askSoon(ctx context.Context, token, audience string) (identity, error) {
	if err := t.take(ctx, t.asking, "token reviews"); err != nil {
		return identity{}, err
	}
	defer func() { <-t.asking }()
	return t.ask(ctx, token, audience)
}

// take takes a slot from slots, which holds the requests of one kind to the
// API server, and fails if none frees up within askWait.
func (t *tokenReviewer) take(ctx context.Context, slots chan struct{}, kind string) error {
	wait := time.NewTimer(t.askWait)
	defer wait.Stop()
	select {
	case slots <- struct{}{}:
		return nil
	case <-wait.C:
		return fmt.Errorf("too many %s are in progress", kind)
	case <-ctx.Done():
		return ctx.Err()
	}
}

// checkWriter checks that the token that id came from is bound to a Pod
// that t.writer owns, and that hasn't finished. Checks of one Pod that
// overlap share one get of the Pod, which goes on if the request that
// started it ends.
func (t *tokenReviewer) checkWriter(ctx context.Context, id identity) error {
	if id.pod == "" || id.podUID == "" {
		return fmt.Errorf("%w: the token isn't bound to a Pod", errDenied)
	}
	name := id.namespace + "/" + id.pod + "/" + id.podUID
	key := sha256.Sum256([]byte(name))
	if r, ok := t.podsDenied.get(key, time.Now()); ok {
		return r.err
	}
	_, err, _ := t.pods.Do(name, func() (any, error) {
		ctx := context.WithoutCancel(ctx)
		if err := t.take(ctx, t.getting, "Pod gets"); err != nil {
			return nil, err
		}
		defer func() { <-t.getting }()
		err := t.checkPod(ctx, id)
		if errors.Is(err, errDenied) {
			t.podsDenied.add(key, review{err: err}, time.Now())
		}
		return nil, err
	})
	return err
}

// pod holds the fields of a Pod that go-cache uses.
type pod struct {
	Metadata struct {
		UID               string            `json:"uid"`
		Labels            map[string]string `json:"labels"`
		DeletionTimestamp string            `json:"deletionTimestamp,omitempty"`
	} `json:"metadata"`
	Status struct {
		Phase string `json:"phase"`
	} `json:"status"`
}

func (t *tokenReviewer) checkPod(ctx context.Context, id identity) error {
	name := id.namespace + "/" + id.pod
	resp, err := t.do(ctx, http.MethodGet, "/api/v1/namespaces/"+url.PathEscape(id.namespace)+"/pods/"+url.PathEscape(id.pod), nil)
	if err != nil {
		return err
	}
	defer resp.Body.Close()
	// etcd holds objects of up to 1.5 MiB.
	b, err := io.ReadAll(io.LimitReader(resp.Body, 4<<20))
	if err != nil {
		return err
	}
	switch resp.StatusCode {
	case http.StatusOK:
	case http.StatusNotFound:
		return fmt.Errorf("%w: the token's Pod %s doesn't exist", errDenied, name)
	default:
		return fmt.Errorf("getting Pod %s: %s: %s", name, resp.Status, bytes.TrimSpace(b))
	}
	var p pod
	if err := json.Unmarshal(b, &p); err != nil {
		return fmt.Errorf("reading Pod %s: %w", name, err)
	}
	switch {
	case p.Metadata.UID != id.podUID:
		return fmt.Errorf("%w: the token is bound to another Pod named %s", errDenied, name)
	case p.Metadata.Labels[controllerLabel] != t.writer:
		return fmt.Errorf("%w: Pod %s isn't %s's", errDenied, name, t.writer)
	case p.Metadata.DeletionTimestamp != "":
		return fmt.Errorf("%w: Pod %s is being deleted", errDenied, name)
	case p.Status.Phase == "Succeeded" || p.Status.Phase == "Failed":
		return fmt.Errorf("%w: Pod %s has finished", errDenied, name)
	}
	return nil
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
			Username string              `json:"username"`
			Extra    map[string][]string `json:"extra,omitempty"`
		} `json:"user"`
		Audiences []string `json:"audiences"`
		Error     string   `json:"error"`
	} `json:"status"`
}

func (t *tokenReviewer) ask(ctx context.Context, token, audience string) (identity, error) {
	tr := tokenReview{APIVersion: "authentication.k8s.io/v1", Kind: "TokenReview"}
	tr.Spec.Token = token
	tr.Spec.Audiences = []string{audience}
	body, err := json.Marshal(tr)
	if err != nil {
		return identity{}, err
	}
	resp, err := t.do(ctx, http.MethodPost, "/apis/authentication.k8s.io/v1/tokenreviews", bytes.NewReader(body))
	if err != nil {
		return identity{}, err
	}
	defer resp.Body.Close()
	b, err := io.ReadAll(io.LimitReader(resp.Body, 1<<20))
	if err != nil {
		return identity{}, err
	}
	if resp.StatusCode != http.StatusCreated && resp.StatusCode != http.StatusOK {
		return identity{}, fmt.Errorf("creating a TokenReview: %s: %s", resp.Status, bytes.TrimSpace(b))
	}
	var got tokenReview
	if err := json.Unmarshal(b, &got); err != nil {
		return identity{}, fmt.Errorf("reading a TokenReview: %w", err)
	}
	return checkReview(&got, audience)
}

// do sends a request to the API server with go-cache's own token.
func (t *tokenReviewer) do(ctx context.Context, method, path string, body io.Reader) (*http.Response, error) {
	own, err := os.ReadFile(t.tokenFile)
	if err != nil {
		return nil, err
	}
	req, err := http.NewRequestWithContext(ctx, method, t.server+path, body)
	if err != nil {
		return nil, err
	}
	req.Header.Set("Authorization", "Bearer "+strings.TrimSpace(string(own)))
	if body != nil {
		req.Header.Set("Content-Type", "application/json")
	}
	req.Header.Set("Accept", "application/json")
	return t.client.Do(req)
}

// checkReview returns the service account that a TokenReview authenticated
// for audience, and the Pod that the token is bound to if the review names
// exactly one. An API server that ignores the requested audiences returns
// none, so a token for any audience passes it; checkReview denies those.
func checkReview(tr *tokenReview, audience string) (identity, error) {
	s := &tr.Status
	switch {
	case !s.Authenticated:
		return identity{}, fmt.Errorf("%w: %s", errDenied, cmp.Or(s.Error, "not authenticated"))
	case !slices.Contains(s.Audiences, audience):
		return identity{}, fmt.Errorf("%w: the token isn't for %s", errDenied, audience)
	}
	rest, ok := strings.CutPrefix(s.User.Username, "system:serviceaccount:")
	ns, name, _ := strings.Cut(rest, ":")
	if !ok || ns == "" || name == "" {
		return identity{}, fmt.Errorf("%w: %s isn't a service account", errDenied, s.User.Username)
	}
	id := identity{namespace: ns}
	if pod, uid := s.User.Extra[podNameExtra], s.User.Extra[podUIDExtra]; len(pod) == 1 && len(uid) == 1 {
		id.pod, id.podUID = pod[0], uid[0]
	}
	return id, nil
}
