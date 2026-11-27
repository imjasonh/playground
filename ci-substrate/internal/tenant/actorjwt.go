package tenant

import (
	"context"
	"crypto"
	"crypto/ecdsa"
	"crypto/elliptic"
	"crypto/rsa"
	"crypto/sha256"
	"crypto/tls"
	"crypto/x509"
	"encoding/base64"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"math/big"
	"net/http"
	"os"
	"slices"
	"strings"
	"sync"
	"time"
)

// ActorIdentity is the verified Substrate actor identity carried by an
// Actor JWT (the actor.ate.dev claim).
type ActorIdentity struct {
	Atespace  string `json:"atespace"`
	ActorName string `json:"actorName"`
	ActorUID  string `json:"actorUID"`
}

// ActorJWTConfig configures verification of Substrate Actor JWTs against
// ate-idp-server's OpenID Connect discovery document and JWKS endpoint.
type ActorJWTConfig struct {
	// Issuer is the trusted iss URL, e.g. "https://idp.ate-system.svc".
	Issuer string
	// Audience is the expected aud value, e.g. "cas.ci-substrate.svc.cluster.local".
	Audience string
	// CAFile is the PEM bundle verifying the issuer's TLS certificate (the
	// servicedns.podcert.ate.dev/identity ClusterTrustBundle in-cluster).
	// Optional when HTTPClient is provided.
	CAFile string
	// HTTPClient overrides the HTTP client used for OIDC discovery and JWKS
	// fetches. Tests set it.
	HTTPClient *http.Client
	// MinRefreshInterval rate-limits JWKS refetches triggered by unknown kids
	// so invalid tokens cannot overload ate-idp-server. Defaults to 10s.
	MinRefreshInterval time.Duration
	// Now returns the current time. Tests set it.
	Now func() time.Time
}

// ActorJWTVerifier verifies Substrate-issued Actor JWTs (ES256 or RS256)
// using OpenID Connect discovery and cached JWKS keys.
type ActorJWTVerifier struct {
	issuer     string
	audience   string
	caFile     string
	httpClient *http.Client
	minRefresh time.Duration
	now        func() time.Time

	mu          sync.Mutex
	jwksURI     string
	keys        map[string]jwkKey
	lastRefresh time.Time
}

type jwkKey struct {
	alg string
	pub crypto.PublicKey
}

// NewActorJWTVerifier returns a verifier for Substrate Actor JWTs.
func NewActorJWTVerifier(cfg ActorJWTConfig) (*ActorJWTVerifier, error) {
	issuer := strings.TrimRight(strings.TrimSpace(cfg.Issuer), "/")
	if issuer == "" || cfg.Audience == "" {
		return nil, errors.New("tenant: actor JWT Issuer and Audience are required")
	}
	if cfg.MinRefreshInterval <= 0 {
		cfg.MinRefreshInterval = 10 * time.Second
	}
	if cfg.Now == nil {
		cfg.Now = time.Now
	}
	v := &ActorJWTVerifier{
		issuer:     issuer,
		audience:   cfg.Audience,
		caFile:     cfg.CAFile,
		httpClient: cfg.HTTPClient,
		minRefresh: cfg.MinRefreshInterval,
		now:        cfg.Now,
		keys:       map[string]jwkKey{},
	}
	return v, nil
}

type jwtHeader struct {
	Typ string `json:"typ"`
	Alg string `json:"alg"`
	Kid string `json:"kid"`
}

type jwtClaims struct {
	Iss   string         `json:"iss"`
	Sub   string         `json:"sub"`
	Aud   []string       `json:"aud"`
	Exp   int64          `json:"exp"`
	Nbf   int64          `json:"nbf"`
	Actor *ActorIdentity `json:"actor.ate.dev"`
}

// Verify parses and cryptographically verifies a Substrate Actor JWT.
func (v *ActorJWTVerifier) Verify(ctx context.Context, raw string) (*ActorIdentity, error) {
	parts := strings.Split(raw, ".")
	if len(parts) != 3 {
		return nil, errors.New("malformed JWT")
	}
	hdrBytes, err := base64.RawURLEncoding.DecodeString(parts[0])
	if err != nil {
		return nil, fmt.Errorf("decoding JWT header: %w", err)
	}
	var hdr jwtHeader
	if err := json.Unmarshal(hdrBytes, &hdr); err != nil {
		return nil, fmt.Errorf("parsing JWT header: %w", err)
	}
	if hdr.Alg != "ES256" && hdr.Alg != "RS256" {
		return nil, fmt.Errorf("unsupported JWT alg %q", hdr.Alg)
	}
	if hdr.Kid == "" {
		return nil, errors.New("missing JWT kid")
	}

	payloadBytes, err := base64.RawURLEncoding.DecodeString(parts[1])
	if err != nil {
		return nil, fmt.Errorf("decoding JWT payload: %w", err)
	}
	var claims jwtClaims
	if err := json.Unmarshal(payloadBytes, &claims); err != nil {
		return nil, fmt.Errorf("parsing JWT payload: %w", err)
	}

	if strings.TrimRight(claims.Iss, "/") != v.issuer {
		return nil, fmt.Errorf("unexpected JWT issuer %q", claims.Iss)
	}
	if !slices.Contains(claims.Aud, v.audience) {
		return nil, fmt.Errorf("JWT missing expected audience %q", v.audience)
	}
	now := v.now().Unix()
	if claims.Exp == 0 || now >= claims.Exp {
		return nil, errors.New("JWT expired")
	}
	if claims.Nbf != 0 && now < claims.Nbf {
		return nil, errors.New("JWT not yet valid")
	}
	// Substrate signs both actor/<atespace>/<name> and
	// worker-for-actor/<atespace>/<name> with the same keys; only accept
	// tokens speaking for the actor itself.
	if !strings.HasPrefix(claims.Sub, "actor/") {
		return nil, fmt.Errorf("JWT subject %q is not an actor subject", claims.Sub)
	}
	if claims.Actor == nil || claims.Actor.Atespace == "" || claims.Actor.ActorName == "" || claims.Actor.ActorUID == "" {
		return nil, errors.New("JWT missing actor.ate.dev claims")
	}
	wantSub := "actor/" + claims.Actor.Atespace + "/" + claims.Actor.ActorName
	if claims.Sub != wantSub {
		return nil, fmt.Errorf("JWT subject %q does not match actor.ate.dev %q", claims.Sub, wantSub)
	}

	sig, err := base64.RawURLEncoding.DecodeString(parts[2])
	if err != nil {
		return nil, fmt.Errorf("decoding JWT signature: %w", err)
	}

	key, err := v.key(ctx, hdr.Kid)
	if err != nil {
		return nil, err
	}
	if key.alg != "" && key.alg != hdr.Alg {
		return nil, fmt.Errorf("JWT alg %q does not match JWK alg %q", hdr.Alg, key.alg)
	}
	signingInput := parts[0] + "." + parts[1]
	if err := verifySignature(hdr.Alg, key.pub, []byte(signingInput), sig); err != nil {
		return nil, fmt.Errorf("invalid JWT signature: %w", err)
	}
	return claims.Actor, nil
}

func (v *ActorJWTVerifier) key(ctx context.Context, kid string) (jwkKey, error) {
	v.mu.Lock()
	defer v.mu.Unlock()
	if k, ok := v.keys[kid]; ok {
		return k, nil
	}
	if !v.lastRefresh.IsZero() && v.now().Sub(v.lastRefresh) < v.minRefresh {
		return jwkKey{}, fmt.Errorf("unknown JWT kid %q", kid)
	}
	if err := v.refreshLocked(ctx); err != nil {
		return jwkKey{}, fmt.Errorf("refreshing JWKS: %w", err)
	}
	k, ok := v.keys[kid]
	if !ok {
		return jwkKey{}, fmt.Errorf("unknown JWT kid %q", kid)
	}
	return k, nil
}

func (v *ActorJWTVerifier) client() (*http.Client, error) {
	if v.httpClient != nil {
		return v.httpClient, nil
	}
	tlsCfg := &tls.Config{MinVersion: tls.VersionTLS13}
	if v.caFile != "" {
		pem, err := os.ReadFile(v.caFile)
		if err != nil {
			return nil, fmt.Errorf("reading actor JWT CA %s: %w", v.caFile, err)
		}
		pool := x509.NewCertPool()
		if !pool.AppendCertsFromPEM(pem) {
			return nil, fmt.Errorf("%s holds no certificates", v.caFile)
		}
		tlsCfg.RootCAs = pool
	}
	return &http.Client{
		Timeout:   10 * time.Second,
		Transport: &http.Transport{TLSClientConfig: tlsCfg},
	}, nil
}

func (v *ActorJWTVerifier) refreshLocked(ctx context.Context) error {
	v.lastRefresh = v.now()
	cli, err := v.client()
	if err != nil {
		return err
	}
	if v.jwksURI == "" {
		var disco struct {
			Issuer  string `json:"issuer"`
			JWKSURI string `json:"jwks_uri"`
		}
		if err := fetchJSON(ctx, cli, v.issuer+"/.well-known/openid-configuration", &disco); err != nil {
			return fmt.Errorf("OIDC discovery: %w", err)
		}
		if strings.TrimRight(disco.Issuer, "/") != v.issuer {
			return fmt.Errorf("OIDC discovery issuer %q != %q", disco.Issuer, v.issuer)
		}
		if disco.JWKSURI == "" {
			return errors.New("OIDC discovery document missing jwks_uri")
		}
		v.jwksURI = disco.JWKSURI
	}

	var jwks struct {
		Keys []rawJWK `json:"keys"`
	}
	if err := fetchJSON(ctx, cli, v.jwksURI, &jwks); err != nil {
		return fmt.Errorf("fetching JWKS: %w", err)
	}
	parsed := make(map[string]jwkKey, len(jwks.Keys))
	for _, rk := range jwks.Keys {
		if rk.Kid == "" || (rk.Use != "" && rk.Use != "sig") {
			continue
		}
		pub, err := rk.publicKey()
		if err != nil {
			continue
		}
		parsed[rk.Kid] = jwkKey{alg: rk.Alg, pub: pub}
	}
	v.keys = parsed
	return nil
}

func fetchJSON(ctx context.Context, cli *http.Client, url string, dst any) error {
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, url, nil)
	if err != nil {
		return err
	}
	resp, err := cli.Do(req)
	if err != nil {
		return err
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return fmt.Errorf("GET %s: status %d", url, resp.StatusCode)
	}
	body, err := io.ReadAll(io.LimitReader(resp.Body, 1<<20))
	if err != nil {
		return err
	}
	return json.Unmarshal(body, dst)
}

type rawJWK struct {
	Kty string `json:"kty"`
	Kid string `json:"kid"`
	Use string `json:"use"`
	Alg string `json:"alg"`
	// EC (P-256)
	Crv string `json:"crv"`
	X   string `json:"x"`
	Y   string `json:"y"`
	// RSA
	N string `json:"n"`
	E string `json:"e"`
}

func (k rawJWK) publicKey() (crypto.PublicKey, error) {
	switch k.Kty {
	case "EC":
		if k.Crv != "P-256" {
			return nil, fmt.Errorf("unsupported curve %q", k.Crv)
		}
		xb, err := base64.RawURLEncoding.DecodeString(k.X)
		if err != nil {
			return nil, err
		}
		yb, err := base64.RawURLEncoding.DecodeString(k.Y)
		if err != nil {
			return nil, err
		}
		x := new(big.Int).SetBytes(xb)
		y := new(big.Int).SetBytes(yb)
		curve := elliptic.P256()
		if !curve.IsOnCurve(x, y) {
			return nil, errors.New("EC point not on P-256")
		}
		return &ecdsa.PublicKey{Curve: curve, X: x, Y: y}, nil
	case "RSA":
		nb, err := base64.RawURLEncoding.DecodeString(k.N)
		if err != nil {
			return nil, err
		}
		eb, err := base64.RawURLEncoding.DecodeString(k.E)
		if err != nil {
			return nil, err
		}
		e := int(new(big.Int).SetBytes(eb).Int64())
		if e < 3 {
			return nil, errors.New("invalid RSA exponent")
		}
		return &rsa.PublicKey{N: new(big.Int).SetBytes(nb), E: e}, nil
	default:
		return nil, fmt.Errorf("unsupported key type %q", k.Kty)
	}
}

func verifySignature(alg string, pub crypto.PublicKey, input, sig []byte) error {
	sum := sha256.Sum256(input)
	switch alg {
	case "ES256":
		ecPub, ok := pub.(*ecdsa.PublicKey)
		if !ok {
			return errors.New("key is not ECDSA")
		}
		if len(sig) != 64 {
			return fmt.Errorf("ES256 signature length %d, want 64", len(sig))
		}
		r := new(big.Int).SetBytes(sig[:32])
		s := new(big.Int).SetBytes(sig[32:])
		if !ecdsa.Verify(ecPub, sum[:], r, s) {
			return errors.New("ECDSA verification failed")
		}
		return nil
	case "RS256":
		rsaPub, ok := pub.(*rsa.PublicKey)
		if !ok {
			return errors.New("key is not RSA")
		}
		return rsa.VerifyPKCS1v15(rsaPub, crypto.SHA256, sum[:], sig)
	default:
		return fmt.Errorf("unsupported alg %q", alg)
	}
}
