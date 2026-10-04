// Package caller identifies the program that sends a request to the core
// program, from the projected service account token in the request's
// Authorization header.
package caller

import (
	"context"
	"errors"
	"fmt"
	"net/http"
	"strings"

	"github.com/imjasonh/playground/kube"
)

// ErrUnauthenticated is wrapped by Identify's errors when the request has
// no token that's valid for the audience.
var ErrUnauthenticated = errors.New("unauthenticated")

// podNameExtra is the extra field of a token that's bound to a Pod that
// holds the Pod's name.
const podNameExtra = "authentication.kubernetes.io/pod-name"

// Caller is the service account that sent a request.
type Caller struct {
	Namespace, Name string
	// Pod is the name of the Pod that the token is bound to, or "" if it
	// isn't bound to a Pod.
	Pod string
}

func (c Caller) String() string { return c.Namespace + "/" + c.Name }

// Check returns the name of the check that the caller runs. kube's
// generate installs each program in a namespace with a service account of
// the program's name, so the check NAME runs as the service account
// check-NAME in the namespace check-NAME, as config/policy.yaml expects.
func (c Caller) Check() (string, bool) {
	name, ok := strings.CutPrefix(c.Name, "check-")
	if !ok || name == "" || c.Namespace != c.Name {
		return "", false
	}
	return name, true
}

// Identify reviews the bearer token in r's Authorization header with
// kube.ReviewToken and returns the service account that it belongs to. The
// token must be valid for audience. A missing or invalid token, or one that
// isn't a service account's, is an error that wraps ErrUnauthenticated.
// Other errors mean that the token couldn't be reviewed.
func Identify(ctx context.Context, r *http.Request, audience string) (Caller, error) {
	scheme, token, _ := strings.Cut(r.Header.Get("Authorization"), " ")
	token = strings.TrimSpace(token)
	if !strings.EqualFold(scheme, "Bearer") || token == "" {
		return Caller{}, fmt.Errorf("%w: send a service account token with the audience %s as a bearer token", ErrUnauthenticated, audience)
	}
	review, err := kube.ReviewToken(ctx, token, audience)
	if err != nil {
		return Caller{}, err
	}
	if !review.Authenticated {
		return Caller{}, fmt.Errorf("%w: %s", ErrUnauthenticated, review.Error)
	}
	ns, name, ok := review.User.ServiceAccount()
	if !ok {
		return Caller{}, fmt.Errorf("%w: %s isn't a service account", ErrUnauthenticated, review.User.Username)
	}
	c := Caller{Namespace: ns, Name: name}
	if pods := review.User.Extra[podNameExtra]; len(pods) == 1 {
		c.Pod = pods[0]
	}
	return c, nil
}
