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
	"strings"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/metadata"
	"google.golang.org/grpc/status"
)

// MetadataKey is the gRPC metadata header that carries a tenant token (or a
// Substrate Actor JWT injected by atenet-egress).
const MetadataKey = "x-ci-substrate-tenant"

// Registry maps tokens to the instance names they may use and tracks whether
// each token may write to the ActionCache directly. When an ActorJWTVerifier
// is configured, Substrate Actor JWTs presented in MetadataKey are also
// accepted and mapped to their atespace's instances.
type Registry struct {
	allow      map[string]map[string]bool
	acReadOnly map[string]bool
	actorJWT   *ActorJWTVerifier
}

// NewRegistry returns an empty registry.
func NewRegistry() *Registry {
	return &Registry{
		allow:      map[string]map[string]bool{},
		acReadOnly: map[string]bool{},
	}
}

// SetActorJWTVerifier enables verification of Substrate Actor JWTs presented
// in MetadataKey.
func (r *Registry) SetActorJWTVerifier(v *ActorJWTVerifier) {
	r.actorJWT = v
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

// AllowReadOnlyAC grants token access to each named instance while denying
// direct ActionCache updates (UpdateActionResult). Developers can use such a
// token to read CI-populated results without poisoning the shared action cache.
func (r *Registry) AllowReadOnlyAC(token string, instances ...string) {
	r.Allow(token, instances...)
	r.acReadOnly[token] = true
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

func (r *Registry) instancesForAtespace(atespace string) map[string]bool {
	out := map[string]bool{}
	for tok, set := range r.allow {
		if r.acReadOnly[tok] || !set[atespace] {
			continue
		}
		for name := range set {
			out[name] = true
		}
	}
	return out
}

func (r *Registry) authenticate(ctx context.Context) (instances map[string]bool, actor *ActorIdentity, readOnlyAC bool, err error) {
	tok := Token(ctx)
	if tok == "" {
		return nil, nil, false, status.Error(codes.Unauthenticated, "missing tenant token")
	}
	if set, ok := r.allow[tok]; ok {
		return set, nil, r.acReadOnly[tok], nil
	}
	if r.actorJWT != nil && strings.Count(tok, ".") == 2 {
		id, err := r.actorJWT.Verify(ctx, tok)
		if err != nil {
			return nil, nil, false, status.Errorf(codes.Unauthenticated, "invalid actor JWT: %v", err)
		}
		set := r.instancesForAtespace(id.Atespace)
		if len(set) == 0 {
			return nil, id, false, status.Errorf(codes.PermissionDenied, "%v: atespace %q", errUnauthorized, id.Atespace)
		}
		return set, id, false, nil
	}
	return nil, nil, false, status.Error(codes.Unauthenticated, "unknown tenant token")
}

// Instances returns a copy of the instance names the caller in ctx may use.
// An unknown, invalid, or missing credential has none.
func (r *Registry) Instances(ctx context.Context) map[string]bool {
	set, _, _, err := r.authenticate(ctx)
	if err != nil {
		return map[string]bool{}
	}
	out := map[string]bool{}
	for name := range set {
		out[name] = true
	}
	return out
}

var errUnauthorized = errors.New("tenant not authorized for instance")

// Authorize returns nil when the caller in ctx may use instanceName, and a
// gRPC status error otherwise. An unknown or missing token is Unauthenticated;
// a known credential reaching for an instance it was not granted is
// PermissionDenied.
func (r *Registry) Authorize(ctx context.Context, instanceName string) error {
	set, _, _, err := r.authenticate(ctx)
	if err != nil {
		return err
	}
	if !set[instanceName] {
		return status.Errorf(codes.PermissionDenied, "%v: %q", errUnauthorized, instanceName)
	}
	return nil
}

// AuthorizeBot verifies that when the caller authenticated with a Substrate
// Actor JWT, the claimed botID matches the JWT's actorName. For static tokens
// it only verifies the token is valid.
func (r *Registry) AuthorizeBot(ctx context.Context, botID string) error {
	_, actor, _, err := r.authenticate(ctx)
	if err != nil {
		return err
	}
	if actor != nil && actor.ActorName != botID {
		return status.Errorf(codes.PermissionDenied, "actor JWT identity %q does not match bot_id %q", actor.ActorName, botID)
	}
	return nil
}

// AuthorizeActionCacheWrite authorizes an ActionCache write for instanceName.
// Tokens configured with AllowReadOnlyAC receive PermissionDenied.
func (r *Registry) AuthorizeActionCacheWrite(ctx context.Context, instanceName string) error {
	set, _, readOnly, err := r.authenticate(ctx)
	if err != nil {
		return err
	}
	if !set[instanceName] {
		return status.Errorf(codes.PermissionDenied, "%v: %q", errUnauthorized, instanceName)
	}
	if readOnly {
		return status.Errorf(codes.PermissionDenied, "token is read-only for action cache on instance %q", instanceName)
	}
	return nil
}
