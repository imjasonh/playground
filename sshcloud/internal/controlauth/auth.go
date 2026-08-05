// Package controlauth authenticates requests between sshcloud control-plane
// workloads. Production authentication deliberately has two independent
// factors: a role URI in a mutually authenticated TLS 1.3 connection and a
// short-lived, audience-bound GCE service-account identity token.
package controlauth

import (
	"bytes"
	"context"
	"encoding/base64"
	"encoding/json"
	"fmt"
	"io"
	"net"
	"net/http"
	"net/url"
	"strconv"
	"strings"
	"time"

	"google.golang.org/api/idtoken"
)

const (
	authorizationHeader   = "Authorization"
	maxIdentityTokenBytes = 64 << 10

	AudienceOrchestratorGateway = "https://control.sshcloud.internal/orchestrator/gateway"
	AudienceOrchestratorAdmin   = "https://control.sshcloud.internal/orchestrator/admin"
	AudienceAgent               = "https://control.sshcloud.internal/agent"
	AudienceAgentServer         = "https://control.sshcloud.internal/agent/server-identity"
	AudienceSnapshot            = "https://control.sshcloud.internal/snapshot"
	AudienceGatewayMigration    = "https://control.sshcloud.internal/gateway/migration"
)

// Role is the exact workload role encoded in a control certificate URI SAN.
type Role string

const (
	RoleGateway      Role = "gateway"
	RoleOrchestrator Role = "orchestrator"
	RoleAgent        Role = "agent"
	RoleSnapshot     Role = "snapshot"
)

var roleURIs = map[Role]string{
	RoleGateway:      "spiffe://sshcloud.internal/control/gateway",
	RoleOrchestrator: "spiffe://sshcloud.internal/control/orchestrator",
	RoleAgent:        "spiffe://sshcloud.internal/control/agent",
	RoleSnapshot:     "spiffe://sshcloud.internal/control/snapshot",
}

// URI returns the one URI SAN permitted for role certificates.
func (r Role) URI() string {
	return roleURIs[r]
}

func validRole(role Role) bool {
	return role.URI() != ""
}

// TokenSource obtains a new audience-bound identity token for one request.
type TokenSource interface {
	Token(context.Context, string) (string, error)
}

// MetadataTokenSource obtains full-format GCE identity documents from the
// metadata server. Full format is required so servers can reject tokens that
// do not carry Compute Engine instance claims.
type MetadataTokenSource struct {
	HTTPClient *http.Client
	BaseURL    string
}

func (s MetadataTokenSource) Token(ctx context.Context, audience string) (string, error) {
	if strings.TrimSpace(audience) == "" {
		return "", fmt.Errorf("identity-token audience is required")
	}
	base := strings.TrimRight(s.BaseURL, "/")
	if base == "" {
		base = "http://metadata.google.internal/computeMetadata/v1"
	}
	endpoint := base + "/instance/service-accounts/default/identity?audience=" +
		url.QueryEscape(audience) + "&format=full"
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, endpoint, nil)
	if err != nil {
		return "", err
	}
	req.Header.Set("Metadata-Flavor", "Google")
	client := s.HTTPClient
	if client == nil {
		client = &http.Client{Timeout: 5 * time.Second}
	}
	res, err := client.Do(req)
	if err != nil {
		return "", fmt.Errorf("get GCE identity token: %w", err)
	}
	defer res.Body.Close()
	if res.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(io.LimitReader(res.Body, 512))
		return "", fmt.Errorf("get GCE identity token: %s: %s", res.Status, strings.TrimSpace(string(body)))
	}
	if res.Header.Get("Metadata-Flavor") != "Google" {
		return "", fmt.Errorf("identity-token response did not come from the GCE metadata service")
	}
	if res.ContentLength == 0 {
		return "", fmt.Errorf("metadata server returned an empty identity token")
	}
	if res.ContentLength > maxIdentityTokenBytes {
		return "", fmt.Errorf("metadata identity token exceeds %d bytes", maxIdentityTokenBytes)
	}
	body, err := io.ReadAll(io.LimitReader(res.Body, maxIdentityTokenBytes+1))
	if err != nil {
		return "", fmt.Errorf("read GCE identity token: %w", err)
	}
	if len(body) > maxIdentityTokenBytes {
		return "", fmt.Errorf("metadata identity token exceeds %d bytes", maxIdentityTokenBytes)
	}
	if res.ContentLength >= 0 && int64(len(body)) != res.ContentLength {
		return "", fmt.Errorf(
			"metadata identity token was truncated: read %d of %d bytes",
			len(body), res.ContentLength,
		)
	}
	token := strings.TrimSpace(string(body))
	if !validIdentityToken(token) {
		if token != "" {
			return "", fmt.Errorf("metadata server returned an invalid identity token")
		}
		return "", fmt.Errorf("metadata server returned an empty identity token")
	}
	return token, nil
}

// RequestAuthorizer adds a fresh metadata identity token to every request.
type RequestAuthorizer struct {
	Source   TokenSource
	Audience string
}

func (a *RequestAuthorizer) Authorize(req *http.Request) error {
	if a == nil || a.Source == nil {
		return fmt.Errorf("control request authorizer is required")
	}
	if req == nil {
		return fmt.Errorf("control request is nil")
	}
	token, err := a.Source.Token(req.Context(), a.Audience)
	if err != nil {
		return err
	}
	if !validIdentityToken(token) {
		return fmt.Errorf("identity-token source returned an invalid token")
	}
	req.Header.Set(authorizationHeader, "Bearer "+token)
	return nil
}

// VerificationPolicy binds one API to one caller role, service account, and
// audience. Role certificates alone are never treated as workload identity.
type VerificationPolicy struct {
	CallerRole     Role
	ServiceAccount string
	Audience       string
}

// TokenVerifier validates the cryptographic token and its GCE workload claims.
type TokenVerifier interface {
	Verify(context.Context, string, VerificationPolicy) error
}

// Identity is the exact Compute Engine workload authenticated by Google. Both
// name and immutable numeric instance ID are required for placement decisions.
type Identity struct {
	ServiceAccount string
	InstanceName   string
	InstanceID     string
	Zone           string
	ProjectID      string
	ProjectNumber  string
}

type IdentityTokenVerifier interface {
	VerifyIdentity(context.Context, string, VerificationPolicy) (Identity, error)
}

// GCEVerifier validates Google signatures/standard JWT claims, token freshness,
// exact service-account email, and the full Compute Engine identity document.
type GCEVerifier struct {
	ProjectID     string
	ProjectNumber string
	MaxTokenAge   time.Duration
	ClockSkew     time.Duration
	Now           func() time.Time
	validate      func(context.Context, string, string) (*idtoken.Payload, error)
}

func (v *GCEVerifier) Verify(ctx context.Context, raw string, policy VerificationPolicy) error {
	_, err := v.VerifyIdentity(ctx, raw, policy)
	return err
}

func (v *GCEVerifier) VerifyIdentity(ctx context.Context, raw string, policy VerificationPolicy) (Identity, error) {
	if v == nil {
		return Identity{}, fmt.Errorf("GCE token verifier is required")
	}
	if !validIdentityToken(raw) {
		return Identity{}, fmt.Errorf("identity token is empty, malformed, or oversized")
	}
	if strings.TrimSpace(policy.Audience) == "" || strings.TrimSpace(policy.ServiceAccount) == "" {
		return Identity{}, fmt.Errorf("token verification policy is incomplete")
	}
	validate := v.validate
	if validate == nil {
		validate = idtoken.Validate
	}
	payload, err := validate(ctx, raw, policy.Audience)
	if err != nil {
		return Identity{}, fmt.Errorf("validate Google identity token: %w", err)
	}
	compute, err := losslessComputeClaims(raw, payload)
	if err != nil {
		return Identity{}, err
	}
	return v.verifyPayloadIdentity(payload, policy, compute)
}

func (v *GCEVerifier) verifyPayloadIdentity(
	payload *idtoken.Payload,
	policy VerificationPolicy,
	exactCompute map[string]any,
) (Identity, error) {
	if payload == nil {
		return Identity{}, fmt.Errorf("Google identity token has no payload")
	}
	if payload.Audience != policy.Audience {
		return Identity{}, fmt.Errorf("identity-token audience %q, want %q", payload.Audience, policy.Audience)
	}
	if payload.Issuer != "https://accounts.google.com" && payload.Issuer != "accounts.google.com" {
		return Identity{}, fmt.Errorf("identity-token issuer %q is not Google", payload.Issuer)
	}
	now := time.Now()
	if v.Now != nil {
		now = v.Now()
	}
	maxAge := v.MaxTokenAge
	if maxAge <= 0 {
		// The metadata server may reuse a still-valid one-hour identity token
		// across calls. Each request still fetches from metadata, but freshness
		// is bounded by Google's expiry rather than assuming a new iat.
		maxAge = 65 * time.Minute
	}
	skew := v.ClockSkew
	if skew <= 0 {
		skew = 30 * time.Second
	}
	issued := time.Unix(payload.IssuedAt, 0)
	if payload.IssuedAt <= 0 || issued.After(now.Add(skew)) {
		return Identity{}, fmt.Errorf("identity token has an invalid issued-at time")
	}
	if now.Sub(issued) > maxAge+skew {
		return Identity{}, fmt.Errorf("identity token is older than %s", maxAge)
	}
	expires := time.Unix(payload.Expires, 0)
	if payload.Expires <= 0 || !expires.After(now.Add(-skew)) {
		return Identity{}, fmt.Errorf("identity token is expired")
	}
	email, _ := payload.Claims["email"].(string)
	if email != policy.ServiceAccount {
		return Identity{}, fmt.Errorf("service-account email %q, want %q", email, policy.ServiceAccount)
	}
	if !claimBool(payload.Claims["email_verified"]) {
		return Identity{}, fmt.Errorf("service-account email is not verified")
	}
	google, ok := payload.Claims["google"].(map[string]any)
	if !ok {
		return Identity{}, fmt.Errorf("identity token is missing full google claims")
	}
	compute, ok := google["compute_engine"].(map[string]any)
	if !ok {
		return Identity{}, fmt.Errorf("identity token is missing full Compute Engine claims")
	}
	if exactCompute != nil {
		compute = exactCompute
	}
	for _, key := range []string{"instance_id", "instance_name", "zone", "project_id", "project_number", "instance_creation_timestamp"} {
		if _, ok := compute[key]; !ok {
			return Identity{}, fmt.Errorf("identity token is missing Compute Engine claim %q", key)
		}
	}
	if projectID, _ := compute["project_id"].(string); projectID == "" || projectID != v.ProjectID {
		return Identity{}, fmt.Errorf("Compute Engine project_id %q, want %q", projectID, v.ProjectID)
	}
	projectNumber, ok := claimIntegerString(compute["project_number"])
	if !ok || projectNumber != v.ProjectNumber {
		return Identity{}, fmt.Errorf("Compute Engine project_number %q, want %q", projectNumber, v.ProjectNumber)
	}
	for _, key := range []string{"instance_id", "instance_creation_timestamp"} {
		if value, ok := claimIntegerString(compute[key]); !ok || value == "" || value == "0" {
			return Identity{}, fmt.Errorf("Compute Engine claim %q is invalid", key)
		}
	}
	for _, key := range []string{"instance_name", "zone"} {
		if value, _ := compute[key].(string); strings.TrimSpace(value) == "" {
			return Identity{}, fmt.Errorf("Compute Engine claim %q is invalid", key)
		}
	}
	instanceID, _ := claimIntegerString(compute["instance_id"])
	instanceName, _ := compute["instance_name"].(string)
	zone, _ := compute["zone"].(string)
	projectID, _ := compute["project_id"].(string)
	return Identity{
		ServiceAccount: email, InstanceName: instanceName, InstanceID: instanceID,
		Zone: zone, ProjectID: projectID, ProjectNumber: projectNumber,
	}, nil
}

func claimBool(value any) bool {
	switch value := value.(type) {
	case bool:
		return value
	case string:
		parsed, _ := strconv.ParseBool(value)
		return parsed
	default:
		return false
	}
}

func claimIntegerString(value any) (string, bool) {
	switch value := value.(type) {
	case string:
		n, err := strconv.ParseUint(value, 10, 64)
		return strconv.FormatUint(n, 10), err == nil
	case json.Number:
		n, err := strconv.ParseUint(value.String(), 10, 64)
		return strconv.FormatUint(n, 10), err == nil
	default:
		return "", false
	}
}

func losslessComputeClaims(raw string, payload *idtoken.Payload) (map[string]any, error) {
	if payload == nil {
		return nil, nil
	}
	google, _ := payload.Claims["google"].(map[string]any)
	compute, _ := google["compute_engine"].(map[string]any)
	needsExact := false
	for _, key := range []string{"instance_id", "project_number", "instance_creation_timestamp"} {
		if _, rounded := compute[key].(float64); rounded {
			needsExact = true
			break
		}
	}
	if !needsExact {
		return nil, nil
	}
	segments := strings.Split(raw, ".")
	if len(segments) != 3 {
		return nil, fmt.Errorf("identity token numeric claims cannot be parsed losslessly")
	}
	claimsJSON, err := base64.RawURLEncoding.DecodeString(segments[1])
	if err != nil {
		return nil, fmt.Errorf("decode identity token claims: %w", err)
	}
	decoder := json.NewDecoder(bytes.NewReader(claimsJSON))
	decoder.UseNumber()
	var claims map[string]any
	if err := decoder.Decode(&claims); err != nil {
		return nil, fmt.Errorf("decode identity token claims: %w", err)
	}
	if err := decoder.Decode(&struct{}{}); err != io.EOF {
		return nil, fmt.Errorf("decode identity token claims: trailing JSON")
	}
	exactGoogle, ok := claims["google"].(map[string]any)
	if !ok {
		return nil, fmt.Errorf("identity token is missing full google claims")
	}
	exactCompute, ok := exactGoogle["compute_engine"].(map[string]any)
	if !ok {
		return nil, fmt.Errorf("identity token is missing full Compute Engine claims")
	}
	out := make(map[string]any, len(compute))
	for key, value := range compute {
		out[key] = value
	}
	for _, key := range []string{"instance_id", "project_number", "instance_creation_timestamp"} {
		if _, rounded := compute[key].(float64); !rounded {
			continue
		}
		value, ok := exactCompute[key]
		if !ok {
			return nil, fmt.Errorf("identity token is missing Compute Engine claim %q", key)
		}
		out[key] = value
	}
	return out, nil
}

// Require enforces both the caller's mTLS role and its GCE identity token.
func Require(verifier TokenVerifier, policy VerificationPolicy, next http.Handler) http.Handler {
	var verify middlewareVerifier
	if verifier != nil {
		verify = func(ctx context.Context, raw string, policy VerificationPolicy) (Identity, error) {
			return Identity{}, verifier.Verify(ctx, raw, policy)
		}
	}
	return require(verify, policy, false, next)
}

type identityContextKey struct{}

// IdentityFromContext returns only the identity installed after signature,
// audience, service account, and full GCE claim verification.
func IdentityFromContext(ctx context.Context) (Identity, bool) {
	identity, ok := ctx.Value(identityContextKey{}).(Identity)
	return identity, ok && identity.InstanceName != "" && identity.InstanceID != ""
}

// RequireIdentity is Require plus verified Compute Engine identity propagation.
// It is used by APIs whose authorization depends on one exact VM incarnation.
func RequireIdentity(verifier IdentityTokenVerifier, policy VerificationPolicy, next http.Handler) http.Handler {
	var verify middlewareVerifier
	if verifier != nil {
		verify = verifier.VerifyIdentity
	}
	return require(verify, policy, true, next)
}

type middlewareVerifier func(context.Context, string, VerificationPolicy) (Identity, error)

func require(
	verifier middlewareVerifier,
	policy VerificationPolicy,
	propagateIdentity bool,
	next http.Handler,
) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		role, err := PeerRole(r)
		if err != nil {
			http.Error(w, "mutual TLS authentication required", http.StatusUnauthorized)
			return
		}
		if role != policy.CallerRole {
			http.Error(w, "caller role is not authorized", http.StatusForbidden)
			return
		}
		raw, ok := bearerToken(r.Header.Values(authorizationHeader))
		if !ok || verifier == nil {
			w.Header().Set("WWW-Authenticate", `Bearer realm="sshcloud-control"`)
			http.Error(w, "unauthorized", http.StatusUnauthorized)
			return
		}
		identity, err := verifier(r.Context(), raw, policy)
		if err != nil {
			w.Header().Set("WWW-Authenticate", `Bearer realm="sshcloud-control"`)
			http.Error(w, "unauthorized", http.StatusUnauthorized)
			return
		}
		if propagateIdentity {
			ctx := context.WithValue(r.Context(), identityContextKey{}, identity)
			r = r.WithContext(ctx)
		}
		next.ServeHTTP(w, r)
	})
}

func bearerToken(values []string) (string, bool) {
	if len(values) != 1 || !strings.HasPrefix(values[0], "Bearer ") {
		return "", false
	}
	token := strings.TrimPrefix(values[0], "Bearer ")
	if !validIdentityToken(token) {
		return "", false
	}
	return token, true
}

func validIdentityToken(token string) bool {
	return token != "" && len(token) <= maxIdentityTokenBytes &&
		strings.TrimSpace(token) == token && !strings.ContainsAny(token, " \t\r\n")
}

// PrepareRequest enforces the production HTTPS+token client path. Tests and
// local development must explicitly request insecure mode, which is restricted
// to literal loopback destinations.
func PrepareRequest(req *http.Request, authorizer *RequestAuthorizer, insecureLoopback bool) error {
	if req == nil || req.URL == nil {
		return fmt.Errorf("control request URL is required")
	}
	if authorizer != nil {
		if req.URL.Scheme != "https" {
			return fmt.Errorf("authenticated control URL must use https")
		}
		return authorizer.Authorize(req)
	}
	if !insecureLoopback {
		return fmt.Errorf("control authentication is required")
	}
	if req.URL.Scheme != "http" || !isLoopbackHost(req.URL.Hostname()) {
		return fmt.Errorf("insecure control mode is limited to loopback HTTP")
	}
	return nil
}

func isLoopbackHost(host string) bool {
	ip := net.ParseIP(strings.Trim(strings.ToLower(host), "[]"))
	return ip != nil && ip.IsLoopback()
}

// ValidateLoopbackListen rejects wildcard/private-network binds for explicit
// insecure local mode.
func ValidateLoopbackListen(address string) error {
	host, _, err := net.SplitHostPort(address)
	if err != nil {
		return fmt.Errorf("invalid control listen address %q: %w", address, err)
	}
	if !isLoopbackHost(host) {
		return fmt.Errorf("insecure control listener %q is not loopback-only", address)
	}
	return nil
}
