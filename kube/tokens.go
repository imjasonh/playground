package kube

import (
	"context"
	"errors"
	"fmt"
	"slices"
	"strings"
	"time"

	"github.com/imjasonh/playground/kube/internal/client"
)

// TokenReview is what the API server says about a bearer token.
type TokenReview struct {
	// Authenticated reports whether the token is valid for one of the
	// audiences that ReviewToken asked for.
	Authenticated bool `json:"authenticated,omitempty"`
	// User is the user or service account that the token belongs to.
	User UserInfo `json:"user,omitzero"`
	// Audiences are the audiences that ReviewToken asked for that the token
	// is valid for. When ReviewToken asks for none, they're the API
	// server's own audiences.
	Audiences []string `json:"audiences,omitempty"`
	// Error says why the token isn't authenticated.
	Error string `json:"error,omitempty"`
}

// UserInfo is a user or service account as the API server knows it.
type UserInfo struct {
	// Username is "system:serviceaccount:NAMESPACE:NAME" for a service
	// account.
	Username string   `json:"username,omitempty"`
	UID      string   `json:"uid,omitempty"`
	Groups   []string `json:"groups,omitempty"`
	// Extra holds more about the user. A token that's bound to a Pod has
	// the Pod's name and UID under "authentication.kubernetes.io/pod-name"
	// and "authentication.kubernetes.io/pod-uid".
	Extra map[string][]string `json:"extra,omitempty"`
}

const (
	podNameExtra = "authentication.kubernetes.io/pod-name"
	podUIDExtra  = "authentication.kubernetes.io/pod-uid"
)

// ServiceAccount returns the namespace and name of the service account that
// u is, or false if u isn't a service account.
func (u UserInfo) ServiceAccount() (namespace, name string, ok bool) {
	rest, ok := strings.CutPrefix(u.Username, "system:serviceaccount:")
	if !ok {
		return "", "", false
	}
	namespace, name, ok = strings.Cut(rest, ":")
	if !ok || namespace == "" || name == "" || strings.Contains(name, ":") {
		return "", "", false
	}
	return namespace, name, true
}

// services are what ReviewToken, RequestToken, and Trigger need from a
// world.
type services interface {
	reviewToken(ctx context.Context, token string, audiences []string) (TokenReview, error)
	requestToken(ctx context.Context, audience string, lifetime time.Duration) (string, time.Time, error)
	trigger(ti *typeInfo, k Key) bool
}

// ReviewToken asks the API server whether token, a bearer token that a
// client sent, is valid, and whose it is. Pass the audiences that your
// server accepts, such as the audience that clients put in their projected
// service account tokens. The token is then authenticated only if it's
// valid for one of them, so a token meant for another server, or for the
// API server, doesn't pass. With no audiences, the API server checks the
// token against its own audiences, and any token that can call the API
// server passes.
//
// An invalid or expired token isn't an error. The review then has
// Authenticated false and the reason in Error. ReviewToken returns an error
// when it can't ask, for example because the program may not create
// TokenReviews. The generate command grants that permission to a program
// that calls ReviewToken.
func ReviewToken(ctx context.Context, token string, audiences ...string) (TokenReview, error) {
	s := scopeFrom(ctx, "ReviewToken")
	if token == "" {
		return TokenReview{Error: "no token"}, nil
	}
	r, err := s.w.reviewToken(ctx, token, audiences)
	if err != nil {
		return TokenReview{}, err
	}
	// A token from an authenticator that doesn't check audiences comes back
	// with none, and might be meant for any server.
	if len(audiences) > 0 && r.Authenticated && !slices.ContainsFunc(r.Audiences, func(a string) bool { return slices.Contains(audiences, a) }) {
		return TokenReview{Error: fmt.Sprintf("the token isn't valid for the audiences %q", audiences)}, nil
	}
	return r, nil
}

// RequestToken returns a new token for the program's own service account,
// valid for audience, and the time that it expires. Use it to prove the
// program's identity to a server that trusts the cluster's service account
// tokens, such as Octo STS, or to another program that checks tokens with
// ReviewToken.
//
// The program finds its service account by asking the API server who it
// is, so RequestToken works with the in-cluster service account and with a
// kubeconfig that holds a service account's token. When the program uses
// its Pod's token, the new token is bound to the Pod too, so it stops
// working when the Pod is deleted.
//
// The token lasts for lifetime, or an hour if lifetime is zero. The API
// server issues no token for less than 10 minutes and may shorten long
// lifetimes, so rely on the returned expiry. Each call returns a new token;
// to make fewer requests, reuse a token until shortly before it expires. The
// generate command grants a program that calls RequestToken permission to
// request tokens for its own service account and no other.
func RequestToken(ctx context.Context, audience string, lifetime time.Duration) (token string, expires time.Time, err error) {
	s := scopeFrom(ctx, "RequestToken")
	switch {
	case audience == "":
		return "", time.Time{}, errors.New("kube.RequestToken: the token needs an audience")
	case lifetime != 0 && lifetime < 10*time.Minute:
		return "", time.Time{}, fmt.Errorf("kube.RequestToken: a lifetime of %v is shorter than the API server's minimum of 10 minutes", lifetime)
	}
	return s.w.requestToken(ctx, audience, lifetime)
}

func (m *Manager) reviewToken(ctx context.Context, token string, audiences []string) (TokenReview, error) {
	var out struct {
		Status TokenReview `json:"status"`
	}
	if err := m.client.Create(ctx, client.Path("authentication.k8s.io/v1", "tokenreviews", "", ""), map[string]any{
		"apiVersion": "authentication.k8s.io/v1", "kind": "TokenReview",
		"spec": map[string]any{"token": token, "audiences": audiences},
	}, &out); err != nil {
		return TokenReview{}, fmt.Errorf("kube.ReviewToken: %w", err)
	}
	return out.Status, nil
}

// whoami returns the user that the program authenticates as.
func (m *Manager) whoami(ctx context.Context) (UserInfo, error) {
	if u := m.self.Load(); u != nil {
		return *u, nil
	}
	var out struct {
		Status struct {
			UserInfo UserInfo `json:"userInfo"`
		} `json:"status"`
	}
	if err := m.client.Create(ctx, client.Path("authentication.k8s.io/v1", "selfsubjectreviews", "", ""), map[string]any{
		"apiVersion": "authentication.k8s.io/v1", "kind": "SelfSubjectReview",
	}, &out); err != nil {
		return UserInfo{}, err
	}
	m.self.Store(&out.Status.UserInfo)
	return out.Status.UserInfo, nil
}

func (m *Manager) requestToken(ctx context.Context, audience string, lifetime time.Duration) (string, time.Time, error) {
	self, err := m.whoami(ctx)
	if err != nil {
		return "", time.Time{}, fmt.Errorf("kube.RequestToken: finding the program's service account: %w", err)
	}
	ns, name, ok := self.ServiceAccount()
	if !ok {
		return "", time.Time{}, fmt.Errorf("kube.RequestToken: the program runs as %q, not as a service account", self.Username)
	}
	spec := map[string]any{"audiences": []string{audience}}
	if lifetime > 0 {
		spec["expirationSeconds"] = int64(lifetime / time.Second)
	}
	if pod, uid := self.Extra[podNameExtra], self.Extra[podUIDExtra]; len(pod) == 1 && len(uid) == 1 {
		spec["boundObjectRef"] = map[string]any{"apiVersion": "v1", "kind": "Pod", "name": pod[0], "uid": uid[0]}
	}
	var out struct {
		Status struct {
			Token               string    `json:"token"`
			ExpirationTimestamp time.Time `json:"expirationTimestamp"`
		} `json:"status"`
	}
	if err := m.client.Create(ctx, client.Path("v1", "serviceaccounts", ns, name, "token"), map[string]any{
		"apiVersion": "authentication.k8s.io/v1", "kind": "TokenRequest", "spec": spec,
	}, &out); err != nil {
		return "", time.Time{}, fmt.Errorf("kube.RequestToken: %w", err)
	}
	return out.Status.Token, out.Status.ExpirationTimestamp, nil
}
