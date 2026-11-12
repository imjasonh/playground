package tenant

import (
	"context"
	"testing"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/metadata"
	"google.golang.org/grpc/status"
)

func ctxWith(token string) context.Context {
	if token == "" {
		return metadata.NewIncomingContext(context.Background(), metadata.MD{})
	}
	return metadata.NewIncomingContext(context.Background(), metadata.Pairs(MetadataKey, token))
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
			err := r.Authorize(ctxWith(tc.token), tc.instance)
			if got := status.Code(err); got != tc.want {
				t.Errorf("Authorize(%q, %q) code = %v, want %v (err %v)", tc.token, tc.instance, got, tc.want, err)
			}
		})
	}
}

func TestTokenRoundTrip(t *testing.T) {
	ctx := ctxWith("tok-a")
	if got := Token(ctx); got != "tok-a" {
		t.Errorf("Token = %q, want tok-a", got)
	}
	if got := Token(context.Background()); got != "" {
		t.Errorf("Token of bare context = %q, want empty", got)
	}
}
