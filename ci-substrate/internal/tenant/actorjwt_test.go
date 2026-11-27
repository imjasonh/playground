package tenant

import (
	"context"
	"crypto"
	"crypto/ecdsa"
	"crypto/elliptic"
	"crypto/rand"
	"crypto/rsa"
	"crypto/sha256"
	"encoding/base64"
	"encoding/json"
	"math/big"
	"net/http"
	"net/http/httptest"
	"sync/atomic"
	"testing"
	"time"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/metadata"
	"google.golang.org/grpc/status"
)

func signES256(t *testing.T, key *ecdsa.PrivateKey, kid string, claims map[string]any) string {
	t.Helper()
	hdr, _ := json.Marshal(map[string]string{"typ": "JWT", "alg": "ES256", "kid": kid})
	pay, _ := json.Marshal(claims)
	input := base64.RawURLEncoding.EncodeToString(hdr) + "." + base64.RawURLEncoding.EncodeToString(pay)
	sum := sha256.Sum256([]byte(input))
	r, s, err := ecdsa.Sign(rand.Reader, key, sum[:])
	if err != nil {
		t.Fatal(err)
	}
	sig := make([]byte, 64)
	r.FillBytes(sig[:32])
	s.FillBytes(sig[32:])
	return input + "." + base64.RawURLEncoding.EncodeToString(sig)
}

func signRS256(t *testing.T, key *rsa.PrivateKey, kid string, claims map[string]any) string {
	t.Helper()
	hdr, _ := json.Marshal(map[string]string{"typ": "JWT", "alg": "RS256", "kid": kid})
	pay, _ := json.Marshal(claims)
	input := base64.RawURLEncoding.EncodeToString(hdr) + "." + base64.RawURLEncoding.EncodeToString(pay)
	sum := sha256.Sum256([]byte(input))
	sig, err := rsa.SignPKCS1v15(rand.Reader, key, crypto.SHA256, sum[:])
	if err != nil {
		t.Fatal(err)
	}
	return input + "." + base64.RawURLEncoding.EncodeToString(sig)
}

func ecJWK(kid string, pub *ecdsa.PublicKey) map[string]string {
	xb, yb := make([]byte, 32), make([]byte, 32)
	pub.X.FillBytes(xb)
	pub.Y.FillBytes(yb)
	return map[string]string{
		"kty": "EC", "kid": kid, "use": "sig", "alg": "ES256", "crv": "P-256",
		"x": base64.RawURLEncoding.EncodeToString(xb),
		"y": base64.RawURLEncoding.EncodeToString(yb),
	}
}

func rsaJWK(kid string, pub *rsa.PublicKey) map[string]string {
	return map[string]string{
		"kty": "RSA", "kid": kid, "use": "sig", "alg": "RS256",
		"n": base64.RawURLEncoding.EncodeToString(pub.N.Bytes()),
		"e": base64.RawURLEncoding.EncodeToString(big.NewInt(int64(pub.E)).Bytes()),
	}
}

func incomingCtx(t *testing.T, tok string) context.Context {
	t.Helper()
	return metadata.NewIncomingContext(t.Context(), metadata.Pairs(MetadataKey, tok))
}

func TestActorJWTVerifierAndRegistry(t *testing.T) {
	ecKey, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	if err != nil {
		t.Fatal(err)
	}
	ecKey2, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	if err != nil {
		t.Fatal(err)
	}
	rsaKey, err := rsa.GenerateKey(rand.Reader, 2048)
	if err != nil {
		t.Fatal(err)
	}

	var jwksFetches atomic.Int32
	keys := []map[string]string{ecJWK("ec-1", &ecKey.PublicKey), rsaJWK("rsa-1", &rsaKey.PublicKey)}

	var srv *httptest.Server
	srv = httptest.NewTLSServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "application/json")
		switch r.URL.Path {
		case "/.well-known/openid-configuration":
			_ = json.NewEncoder(w).Encode(map[string]any{
				"issuer":   srv.URL,
				"jwks_uri": srv.URL + "/openid/v1/jwks",
			})
		case "/openid/v1/jwks":
			jwksFetches.Add(1)
			_ = json.NewEncoder(w).Encode(map[string]any{"keys": keys})
		default:
			http.NotFound(w, r)
		}
	}))
	defer srv.Close()

	now := time.Unix(1_760_400_000, 0)
	v, err := NewActorJWTVerifier(ActorJWTConfig{
		Issuer:             srv.URL,
		Audience:           "cas.ci-substrate.svc.cluster.local",
		HTTPClient:         srv.Client(),
		MinRefreshInterval: 10 * time.Second,
		Now:                func() time.Time { return now },
	})
	if err != nil {
		t.Fatal(err)
	}

	reg := NewRegistry()
	reg.Allow("tok-a", "tenant-a", "shared")
	reg.Allow("tok-b", "tenant-b", "shared")
	reg.Allow("tok-admin", "tenant-a", "tenant-b")
	reg.SetActorJWTVerifier(v)

	validClaims := func(atespace, actor string) map[string]any {
		return map[string]any{
			"iss": srv.URL,
			"sub": "actor/" + atespace + "/" + actor,
			"aud": []string{"cas.ci-substrate.svc.cluster.local"},
			"iat": now.Unix(),
			"nbf": now.Add(-5 * time.Minute).Unix(),
			"exp": now.Add(10 * time.Minute).Unix(),
			"actor.ate.dev": map[string]string{
				"atespace":  atespace,
				"actorName": actor,
				"actorUID":  "4f9c3a1e-8d2b-4c77-9e0a-6b5f1d2c3e4a",
			},
		}
	}

	// Valid ES256 and RS256 tokens authorize only their own atespace (never
	// sibling instances from multi-tenant static tokens) and enforce
	// bot_id == actorName.
	for name, tok := range map[string]string{
		"ES256": signES256(t, ecKey, "ec-1", validClaims("tenant-a", "ci-runner-abc")),
		"RS256": signRS256(t, rsaKey, "rsa-1", validClaims("tenant-a", "ci-runner-abc")),
	} {
		t.Run(name, func(t *testing.T) {
			ctx := incomingCtx(t, tok)
			if err := reg.Authorize(ctx, "tenant-a"); err != nil {
				t.Fatalf("Authorize(tenant-a): %v", err)
			}
			if err := reg.Authorize(ctx, "shared"); status.Code(err) != codes.PermissionDenied {
				t.Fatalf("Authorize(shared) = %v, want PermissionDenied", err)
			}
			if err := reg.Authorize(ctx, "tenant-b"); status.Code(err) != codes.PermissionDenied {
				t.Fatalf("Authorize(tenant-b) = %v, want PermissionDenied", err)
			}
			if err := reg.AuthorizeBot(ctx, "ci-runner-abc"); err != nil {
				t.Fatalf("AuthorizeBot(matching): %v", err)
			}
			if err := reg.AuthorizeBot(ctx, "ci-runner-spoofed"); status.Code(err) != codes.PermissionDenied {
				t.Fatalf("AuthorizeBot(spoofed) = %v, want PermissionDenied", err)
			}
		})
	}

	// Reject invalid tokens.
	badCases := map[string]struct {
		tok  string
		want codes.Code
	}{
		"forged_signature": {
			tok:  signES256(t, ecKey2, "ec-1", validClaims("tenant-a", "ci-runner-abc")),
			want: codes.Unauthenticated,
		},
		"wrong_audience": {
			tok: signES256(t, ecKey, "ec-1", func() map[string]any {
				c := validClaims("tenant-a", "ci-runner-abc")
				c["aud"] = []string{"https://other.example.com"}
				return c
			}()),
			want: codes.Unauthenticated,
		},
		"wrong_issuer": {
			tok: signES256(t, ecKey, "ec-1", func() map[string]any {
				c := validClaims("tenant-a", "ci-runner-abc")
				c["iss"] = "https://evil.example.com"
				return c
			}()),
			want: codes.Unauthenticated,
		},
		"expired": {
			tok: signES256(t, ecKey, "ec-1", func() map[string]any {
				c := validClaims("tenant-a", "ci-runner-abc")
				c["exp"] = now.Add(-time.Second).Unix()
				return c
			}()),
			want: codes.Unauthenticated,
		},
		"worker_for_actor_subject": {
			tok: signES256(t, ecKey, "ec-1", func() map[string]any {
				c := validClaims("tenant-a", "ci-runner-abc")
				c["sub"] = "worker-for-actor/tenant-a/ci-runner-abc"
				return c
			}()),
			want: codes.Unauthenticated,
		},
		"unknown_atespace": {
			tok:  signES256(t, ecKey, "ec-1", validClaims("intruder", "ci-runner-abc")),
			want: codes.PermissionDenied,
		},
	}
	for name, tc := range badCases {
		t.Run("reject_"+name, func(t *testing.T) {
			err := reg.Authorize(incomingCtx(t, tc.tok), "tenant-a")
			if status.Code(err) != tc.want {
				t.Fatalf("Authorize = %v (%v), want %v", status.Code(err), err, tc.want)
			}
		})
	}

	// Unknown kid is rate-limited within MinRefreshInterval, then refreshes
	// once the interval passes (key rotation).
	before := jwksFetches.Load()
	rotatedTok := signES256(t, ecKey2, "ec-2", validClaims("tenant-a", "ci-runner-abc"))
	if err := reg.Authorize(incomingCtx(t, rotatedTok), "tenant-a"); status.Code(err) != codes.Unauthenticated {
		t.Fatalf("unrotated kid = %v, want Unauthenticated", err)
	}
	if jwksFetches.Load() != before {
		t.Fatalf("unknown kid bypassed MinRefreshInterval: fetches %d -> %d", before, jwksFetches.Load())
	}
	keys = append(keys, ecJWK("ec-2", &ecKey2.PublicKey))
	now = now.Add(11 * time.Second)
	if err := reg.Authorize(incomingCtx(t, rotatedTok), "tenant-a"); err != nil {
		t.Fatalf("rotated kid after refresh interval: %v", err)
	}
}
