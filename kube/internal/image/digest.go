package image

import (
	"context"
	"fmt"

	"github.com/google/go-containerregistry/pkg/authn"
	"github.com/google/go-containerregistry/pkg/name"
	"github.com/google/go-containerregistry/pkg/v1/remote"
)

// Digest returns the digest of the manifest or index that ref names, with
// credentials from docker login or podman login, as Push uses. If ref has a
// digest, Digest returns it without asking the registry.
func Digest(ctx context.Context, ref string) (string, error) {
	r, err := name.ParseReference(ref)
	if err != nil {
		return "", fmt.Errorf("image: %w", err)
	}
	if d, ok := r.(name.Digest); ok {
		return d.DigestStr(), nil
	}
	if desc, err := remote.Head(r, options(ctx)...); err == nil {
		return desc.Digest.String(), nil
	}
	// A registry that doesn't answer HEAD, or answers without the digest,
	// still answers GET, and a GET that fails has the registry's error.
	desc, err := remote.Get(r, options(ctx)...)
	if err != nil {
		return "", fmt.Errorf("image: reading %s: %w", ref, err)
	}
	return desc.Digest.String(), nil
}

// options returns the options for reading and writing images in a registry.
func options(ctx context.Context) []remote.Option {
	return []remote.Option{remote.WithContext(ctx), remote.WithAuthFromKeychain(authn.DefaultKeychain), remote.WithUserAgent("kube-generate")}
}
