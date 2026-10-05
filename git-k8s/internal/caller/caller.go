// Package caller identifies the program that sends a request to the core
// program, from the projected service account token in the request's
// Authorization header, and the check that the program runs.
package caller

import (
	"context"
	"errors"
	"fmt"
	"net/http"
	"strings"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
)

// ChecksNamespace and ChecksConfigMap name the git-k8s-checks ConfigMap,
// which maps service accounts to checks. The admission policies in
// config/policy.yaml read the same ConfigMap, and name the same service
// account as the core program's.
const (
	ChecksNamespace = "git-k8s"
	ChecksConfigMap = "git-k8s-checks"
	coreAccount     = "git-k8s.git-k8s"
)

// ErrUnauthenticated is wrapped by Identify's errors when the request has
// no token that's valid for the audience.
var ErrUnauthenticated = errors.New("unauthenticated")

// podNameExtra and podUIDExtra are the extra fields of a token that's bound
// to a Pod that hold the Pod's name and UID.
const (
	podNameExtra = "authentication.kubernetes.io/pod-name"
	podUIDExtra  = "authentication.kubernetes.io/pod-uid"
)

// Caller is the service account that sent a request.
type Caller struct {
	Namespace, Name string
	// Pod and PodUID are the name and UID of the Pod that the token is
	// bound to, or "" if it isn't bound to a Pod.
	Pod, PodUID string
}

func (c Caller) String() string { return c.Namespace + "/" + c.Name }

// Checks returns the data of the git-k8s-checks ConfigMap, the entries that
// Check takes, or no entries if the ConfigMap doesn't exist.
func Checks(ctx context.Context) (map[string]string, error) {
	cm, err := kube.Fetch[k8s.ConfigMap](ctx, ChecksNamespace, ChecksConfigMap)
	if err != nil || cm == nil {
		return nil, err
	}
	return cm.Data, nil
}

// Check returns the name of the check that the caller runs. Each of
// entries, the data of the git-k8s-checks ConfigMap, maps
// NAMESPACE.SERVICE_ACCOUNT to a check's name, or to "" for a service
// account that isn't a check. Without an entry, generate's convention
// applies: it installs each program in a namespace with a service account
// of the program's name, so the check NAME runs as the service account
// check-NAME in the namespace check-NAME. The core program's service
// account is never a check. The check variable of the policies in
// config/policy.yaml maps service accounts the same way, so change both
// together.
func (c Caller) Check(entries map[string]string) (string, bool) {
	account := c.Namespace + "." + c.Name
	if account == coreAccount {
		return "", false
	}
	if check, ok := entries[account]; ok {
		return check, check != ""
	}
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
	if pods, uids := review.User.Extra[podNameExtra], review.User.Extra[podUIDExtra]; len(pods) == 1 && len(uids) == 1 {
		c.Pod, c.PodUID = pods[0], uids[0]
	}
	return c, nil
}
