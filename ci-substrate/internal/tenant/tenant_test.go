package tenant

import (
	"context"
	"testing"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/metadata"
	"google.golang.org/grpc/status"
)

func ctxWith(t *testing.T, token string) context.Context {
	t.Helper()
	if token == "" {
		return metadata.NewIncomingContext(t.Context(), metadata.MD{})
	}
	return metadata.NewIncomingContext(t.Context(), metadata.Pairs(MetadataKey, token))
}

func TestAuthorize(t *testing.T) {
	r := NewRegistry()
	r.Allow("tok-a", "tenant-a", "shared")
	r.Allow("tok-b", "tenant-b", "shared")

	cases := []struct {
		name     string
		token    string
		instance string
		want     codes.Code
	}{
		{"own instance", "tok-a", "tenant-a", codes.OK},
		{"shared instance", "tok-a", "shared", codes.OK},
		{"cross tenant denied", "tok-a", "tenant-b", codes.PermissionDenied},
		{"other side denied", "tok-b", "tenant-a", codes.PermissionDenied},
		{"unknown token", "tok-x", "shared", codes.Unauthenticated},
		{"no token", "", "shared", codes.Unauthenticated},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			err := r.Authorize(ctxWith(t, tc.token), tc.instance)
			if got := status.Code(err); got != tc.want {
				t.Errorf("Authorize(%q, %q) code = %v, want %v (err %v)", tc.token, tc.instance, got, tc.want, err)
			}
		})
	}
}

func TestTokenRoundTrip(t *testing.T) {
	ctx := ctxWith(t, "tok-a")
	if got := Token(ctx); got != "tok-a" {
		t.Errorf("Token = %q, want tok-a", got)
	}
	if got := Token(t.Context()); got != "" {
		t.Errorf("Token of bare context = %q, want empty", got)
	}
}
