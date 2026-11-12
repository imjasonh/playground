package tenant

import (
	"context"
	"testing"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/metadata"
	"google.golang.org/grpc/status"
)

func TestLoadJSON(t *testing.T) {
	r, err := LoadJSON([]byte(`{"tok-a":["tenant-a","shared"],"tok-b":["tenant-b","shared"]}`))
	if err != nil {
		t.Fatal(err)
	}
	ctx := metadata.NewIncomingContext(context.Background(), metadata.Pairs(MetadataKey, "tok-a"))
	if err := r.Authorize(ctx, "tenant-a"); err != nil {
		t.Errorf("tok-a should reach tenant-a: %v", err)
	}
	if got := status.Code(r.Authorize(ctx, "tenant-b")); got != codes.PermissionDenied {
		t.Errorf("tok-a reaching tenant-b: code %v, want PermissionDenied", got)
	}
}

func TestLoadJSONBad(t *testing.T) {
	if _, err := LoadJSON([]byte("not json")); err == nil {
		t.Error("LoadJSON accepted invalid JSON")
	}
}
