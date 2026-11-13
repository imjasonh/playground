// Package tenant enforces the multi-tenancy boundary of the control plane. A
// tenant presents an opaque token on every request; the token decides which
// Remote Execution instance names that caller may read from and write to.
//
// Instance names are the isolation unit. Each CI tenant gets a private
// instance (its own action cache and uploads), and tenants that opt into
// shared, content-addressed data read a common instance such as "shared". A
// token scoped only to "tenant-a" cannot touch "tenant-b", which is how one
// tenant's build results stay invisible to another even though every blob
// lives in one physical store.
package tenant

import (
	"context"
	"errors"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/metadata"
	"google.golang.org/grpc/status"
)

// MetadataKey is the gRPC metadata header that carries a tenant token.
const MetadataKey = "x-ci-substrate-tenant"

// Registry maps tokens to the instance names they may use.
type Registry struct {
	allow map[string]map[string]bool
}

// NewRegistry returns an empty registry.
func NewRegistry() *Registry {
	return &Registry{allow: map[string]map[string]bool{}}
}

// Allow grants token access to each named instance. Calling it again for the
// same token adds to the set.
func (r *Registry) Allow(token string, instances ...string) {
	set := r.allow[token]
	if set == nil {
		set = map[string]bool{}
		r.allow[token] = set
	}
	for _, name := range instances {
		set[name] = true
	}
}

// TokenFor returns a token that may use instanceName, for a component that
// acts for a tenant on the tenant's behalf: the node agent that hydrates an
// actor's inputs holds the tenant table, the way cascache does, and fetches
// as the tenant whose volume it serves. When several tokens may use the
// instance it returns the smallest, so the choice is stable. It reports
// false when none may.
func (r *Registry) TokenFor(instanceName string) (string, bool) {
	best, found := "", false
	for tok, set := range r.allow {
		if set[instanceName] && (!found || tok < best) {
			best, found = tok, true
		}
	}
	return best, found
}

// Token returns the tenant token carried by ctx, or "" when none is present.
func Token(ctx context.Context) string {
	md, ok := metadata.FromIncomingContext(ctx)
	if !ok {
		return ""
	}
	vals := md.Get(MetadataKey)
	if len(vals) == 0 {
		return ""
	}
	return vals[0]
}

// Outgoing attaches token to ctx for a client call.
func Outgoing(ctx context.Context, token string) context.Context {
	return metadata.AppendToOutgoingContext(ctx, MetadataKey, token)
}

// Instances returns a copy of the instance names the token in ctx may use. An
// unknown or missing token has none.
func (r *Registry) Instances(ctx context.Context) map[string]bool {
	out := map[string]bool{}
	for name := range r.allow[Token(ctx)] {
		out[name] = true
	}
	return out
}

var errUnauthorized = errors.New("tenant not authorized for instance")

// Authorize returns nil when the token in ctx may use instanceName, and a gRPC
// status error otherwise. An unknown or missing token is Unauthenticated; a
// known token reaching for an instance it was not granted is PermissionDenied.
func (r *Registry) Authorize(ctx context.Context, instanceName string) error {
	tok := Token(ctx)
	if tok == "" {
		return status.Error(codes.Unauthenticated, "missing tenant token")
	}
	set, ok := r.allow[tok]
	if !ok {
		return status.Error(codes.Unauthenticated, "unknown tenant token")
	}
	if !set[instanceName] {
		return status.Errorf(codes.PermissionDenied, "%v: %q", errUnauthorized, instanceName)
	}
	return nil
}
