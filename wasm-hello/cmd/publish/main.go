// Command publish pushes a wasm module to a registry as an OCI artifact.
//
// CI runs this on every push to main so the iOS Wasm Service experiment has
// something to pull. It also works by hand against any registry you can log
// in to, which is the point of keeping the reference configurable in the app.
//
//	go run ./cmd/publish --module hello.wasm --repo ghcr.io/you/wasm-hello
//	go run ./cmd/publish --module hello.wasm --repo whatever --dry-run
package main

import (
	"context"
	"flag"
	"fmt"
	"os"
	"os/signal"
	"path/filepath"
	"strings"
	"syscall"

	"github.com/google/go-containerregistry/pkg/authn"
	"github.com/google/go-containerregistry/pkg/authn/github"
	"github.com/google/go-containerregistry/pkg/v1/remote"
	"github.com/imjasonh/playground/wasm-hello/internal/publish"
)

type repeated []string

func (r *repeated) String() string { return strings.Join(*r, ",") }

func (r *repeated) Set(value string) error {
	if value == "" {
		return fmt.Errorf("empty value")
	}
	*r = append(*r, value)
	return nil
}

func main() {
	var (
		module      = flag.String("module", "hello.wasm", "wasm module to publish")
		repo        = flag.String("repo", "", "repository to push to, e.g. ghcr.io/imjasonh/playground/wasm-hello")
		dryRun      = flag.Bool("dry-run", false, "print the manifest and push nothing")
		tags        repeated
		annotations repeated
	)
	flag.Var(&tags, "tag", "tag to push (repeatable; default latest)")
	flag.Var(&annotations, "annotation", "manifest annotation as key=value (repeatable)")
	flag.Parse()

	if err := run(*module, *repo, tags, annotations, *dryRun); err != nil {
		fmt.Fprintln(os.Stderr, "publish:", err)
		os.Exit(1)
	}
}

func run(module, repo string, tags, annotations []string, dryRun bool) error {
	contents, err := os.ReadFile(module)
	if err != nil {
		return err
	}
	parsed, err := parseAnnotations(annotations)
	if err != nil {
		return err
	}
	artifact, err := publish.Build(contents, filepath.Base(module), parsed)
	if err != nil {
		return err
	}

	if dryRun {
		pretty, err := artifact.Pretty()
		if err != nil {
			return err
		}
		fmt.Println(pretty)
		return nil
	}

	if repo == "" {
		return fmt.Errorf("--repo is required")
	}
	if len(tags) == 0 {
		tags = []string{"latest"}
	}

	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()

	// GITHUB_TOKEN covers CI; the docker config covers a laptop that has run
	// `docker login`. Neither is required to build, only to push.
	keychain := authn.NewMultiKeychain(github.Keychain, authn.DefaultKeychain)
	fmt.Fprintf(os.Stderr, "pushing %s (%d bytes) to %s\n", filepath.Base(module), len(contents), repo)

	reference, err := publish.Push(ctx, repo, tags, artifact, remote.WithAuthFromKeychain(keychain))
	if err != nil {
		return err
	}
	// Only the digest reference on stdout, so a caller can capture it.
	fmt.Println(reference)
	return nil
}

func parseAnnotations(pairs []string) (map[string]string, error) {
	if len(pairs) == 0 {
		return nil, nil
	}
	out := make(map[string]string, len(pairs))
	for _, pair := range pairs {
		key, value, ok := strings.Cut(pair, "=")
		if !ok || key == "" {
			return nil, fmt.Errorf("annotation %q is not key=value", pair)
		}
		out[key] = value
	}
	return out, nil
}
