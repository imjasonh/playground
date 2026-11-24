package tenant

import (
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
	ctx := metadata.NewIncomingContext(t.Context(), metadata.Pairs(MetadataKey, "tok-a"))
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

func TestLoadJSONActionCacheReadOnly(t *testing.T) {
	r, err := LoadJSON([]byte(`{
		"tok-ci": ["tenant-a"],
		"tok-dev": {"instances": ["tenant-a"], "action_cache_read_only": true}
	}`))
	if err != nil {
		t.Fatal(err)
	}
	ciCtx := metadata.NewIncomingContext(t.Context(), metadata.Pairs(MetadataKey, "tok-ci"))
	devCtx := metadata.NewIncomingContext(t.Context(), metadata.Pairs(MetadataKey, "tok-dev"))

	if err := r.AuthorizeActionCacheWrite(ciCtx, "tenant-a"); err != nil {
		t.Errorf("tok-ci AC write denied: %v", err)
	}
	if err := r.Authorize(devCtx, "tenant-a"); err != nil {
		t.Errorf("tok-dev read denied: %v", err)
	}
	if got := status.Code(r.AuthorizeActionCacheWrite(devCtx, "tenant-a")); got != codes.PermissionDenied {
		t.Errorf("tok-dev AC write code = %v, want PermissionDenied", got)
	}
}
