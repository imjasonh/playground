package kube

import (
	"context"
	"crypto/sha256"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
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
	// is valid for.
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
	requestToken(ctx context.Context, audience string) (string, time.Time, error)
	trigger(ti *typeInfo, k Key) bool
}

// ReviewToken asks the API server whether token, a bearer token that a
// client sent, is valid for audience or for any audience in more, and whose
// it is. Pass the audiences that your server accepts, such as the audience
// that clients put in their projected service account tokens. A token meant
// for another server, or for the API server, doesn't pass, so a token that
// your server receives can't call the API server.
//
// An invalid or expired token isn't an error. The review then has
// Authenticated false and the reason in Error. ReviewToken returns an error
// when an audience is empty, and when it can't ask, for example because the
// program may not create TokenReviews. The generate command grants that
// permission to a program that calls ReviewToken.
func ReviewToken(ctx context.Context, token, audience string, more ...string) (TokenReview, error) {
	s := scopeFrom(ctx, "ReviewToken")
	audiences := append([]string{audience}, more...)
	if slices.Contains(audiences, "") {
		return TokenReview{}, errors.New("kube.ReviewToken: an audience is empty")
	}
	if token == "" {
		return TokenReview{Error: "no token"}, nil
	}
	r, err := s.w.reviewToken(ctx, token, audiences)
	if err != nil {
		return TokenReview{}, err
	}
	// A token from an authenticator that doesn't check audiences comes back
	// with none, and might be meant for any server.
	if r.Authenticated && !slices.ContainsFunc(r.Audiences, func(a string) bool { return slices.Contains(audiences, a) }) {
		return TokenReview{Error: fmt.Sprintf("the token isn't valid for the audiences %q", audiences)}, nil
	}
	return r, nil
}

// RequestToken returns a token for the program's own service account, valid
// for audience, and the time that it expires. Use it to prove the program's
// identity to a server that trusts the cluster's service account tokens,
// such as Octo STS, or to another program that checks tokens with
// ReviewToken.
//
// Pass the audience as a constant, such as "octo-sts.dev". The generate
// command then has the kubelet mount a token for each such audience into the
// program's Pod and renew it, and RequestToken reads that token from
// Manager.TokenDir. The token is bound to the Pod, so it stops working when
// the Pod is deleted, and the program needs no permission to request
// tokens.
//
// For an audience without a mounted token, RequestToken asks the API server
// for a new token with a TokenRequest. The program finds its service account
// by asking the API server who it is, so this works with the in-cluster
// service account and with a kubeconfig that holds a service account's
// token. When the program uses its Pod's token, the new token is bound to
// the Pod too. The generate command grants permission to request tokens for
// the program's own service account, and no other, only to a program that
// passes RequestToken an audience that isn't a constant.
//
// A token lasts about an hour, so rely on the returned expiry. The kubelet
// renews a mounted token when 80% of that time has passed, and a
// TokenRequest returns a new token on each call, so call RequestToken each
// time you need a token, or reuse one until shortly before it expires.
func RequestToken(ctx context.Context, audience string) (token string, expires time.Time, err error) {
	s := scopeFrom(ctx, "RequestToken")
	if audience == "" {
		return "", time.Time{}, errors.New("kube.RequestToken: the token needs an audience")
	}
	return s.w.requestToken(ctx, audience)
}

// tokenFile is the name of the file in Manager.TokenDir that holds the
// token for audience.
func tokenFile(audience string) string {
	sum := sha256.Sum256([]byte(audience))
	return hex.EncodeToString(sum[:])
}

// tokenExpiry returns when a service account token expires, from its exp
// claim. It doesn't check the token's signature.
func tokenExpiry(token string) (time.Time, error) {
	parts := strings.Split(token, ".")
	if len(parts) != 3 {
		return time.Time{}, errors.New("not a JSON Web Token")
	}
	b, err := base64.RawURLEncoding.DecodeString(parts[1])
	if err != nil {
		return time.Time{}, fmt.Errorf("decoding the claims: %w", err)
	}
	var claims struct {
		Exp int64 `json:"exp"`
	}
	if err := json.Unmarshal(b, &claims); err != nil {
		return time.Time{}, fmt.Errorf("decoding the claims: %w", err)
	}
	if claims.Exp == 0 {
		return time.Time{}, errors.New("no exp claim")
	}
	return time.Unix(claims.Exp, 0), nil
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

func (m *Manager) requestToken(ctx context.Context, audience string) (string, time.Time, error) {
	if m.TokenDir != "" {
		file := filepath.Join(m.TokenDir, tokenFile(audience))
		b, err := os.ReadFile(file) // #nosec G304 -- a file named by a hash, in the directory that -token-dir names.
		switch {
		case err == nil:
			token := strings.TrimSpace(string(b))
			expires, err := tokenExpiry(token)
			if err != nil {
				return "", time.Time{}, fmt.Errorf("kube.RequestToken: the token for %q in %s: %w", audience, file, err)
			}
			if !time.Now().Before(expires) {
				return "", time.Time{}, fmt.Errorf("kube.RequestToken: the token for %q in %s expired at %v", audience, file, expires)
			}
			return token, expires, nil
		case !errors.Is(err, fs.ErrNotExist):
			return "", time.Time{}, fmt.Errorf("kube.RequestToken: %w", err)
		}
	}
	self, err := m.whoami(ctx)
	if err != nil {
		return "", time.Time{}, fmt.Errorf("kube.RequestToken: finding the program's service account: %w", err)
	}
	ns, name, ok := self.ServiceAccount()
	if !ok {
		return "", time.Time{}, fmt.Errorf("kube.RequestToken: the program runs as %q, not as a service account", self.Username)
	}
	spec := map[string]any{"audiences": []string{audience}}
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
