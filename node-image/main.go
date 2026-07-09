package main

import (
	"flag"
	"fmt"
	"os"
	"strings"

	"github.com/imjasonh/playground/node-image/internal/buildcmd"
)

func main() {
	if len(os.Args) < 2 {
		usage()
		os.Exit(2)
	}
	switch os.Args[1] {
	case "build":
		if err := runBuild(os.Args[2:]); err != nil {
			fmt.Fprintf(os.Stderr, "node-image: %v\n", err)
			os.Exit(1)
		}
	case "version", "-version", "--version":
		fmt.Println("node-image 0.0.0-dev")
	case "help", "-h", "--help":
		usage()
	default:
		fmt.Fprintf(os.Stderr, "unknown command %q\n", os.Args[1])
		usage()
		os.Exit(2)
	}
}

func runBuild(args []string) error {
	fs := flag.NewFlagSet("build", flag.ContinueOnError)
	fs.SetOutput(os.Stderr)
	repo := fs.String("repo", "", "destination repository (required unless --no-push)")
	base := fs.String("base", "", "base image (default from config / distroless node)")
	platform := fs.String("platform", "", "comma-separated platforms (default linux/amd64,linux/arm64)")
	tag := fs.String("t", "", "comma-separated tags")
	skipBuild := fs.Bool("skip-build", false, "skip pnpm run build even if scripts.build exists")
	noPush := fs.Bool("no-push", false, "do not push; write digest summary instead")
	local := fs.Bool("local", false, "load image into local Docker daemon instead of pushing")
	fs.BoolVar(local, "L", false, "shorthand for --local")
	ociDir := fs.String("oci-dir", "", "output directory for --no-push digest summary")
	emptyBase := fs.Bool("empty-base", false, "use scratch instead of pulling base (testing)")
	maxLayers := fs.Int("max-layers", 0, "max total image layers including base (default 127)")
	dir, flagArgs := splitDirAndFlags(args)
	if err := fs.Parse(flagArgs); err != nil {
		return err
	}
	if fs.NArg() > 0 {
		return fmt.Errorf("unexpected arguments: %v", fs.Args())
	}
	var platforms []string
	if *platform != "" {
		platforms = splitCSV(*platform)
	}
	var tags []string
	if *tag != "" {
		tags = splitCSV(*tag)
	}
	_, err := buildcmd.Run(buildcmd.Options{
		Dir:       dir,
		Repo:      *repo,
		Base:      *base,
		Platforms: platforms,
		Tags:      tags,
		SkipBuild: *skipBuild,
		NoPush:    *noPush,
		Local:     *local,
		OCIDir:    *ociDir,
		EmptyBase: *emptyBase,
		MaxLayers: *maxLayers,
	})
	return err
}

// splitDirAndFlags allows either `build [dir] --flags` or `build --flags [dir]`.
func splitDirAndFlags(args []string) (dir string, flagArgs []string) {
	dir = "."
	if len(args) == 0 {
		return dir, nil
	}
	if !strings.HasPrefix(args[0], "-") {
		return args[0], args[1:]
	}
	// Flags first: peel a trailing non-flag directory if present.
	last := args[len(args)-1]
	if !strings.HasPrefix(last, "-") {
		return last, args[:len(args)-1]
	}
	return dir, args
}

func splitCSV(s string) []string {
	parts := strings.Split(s, ",")
	out := make([]string, 0, len(parts))
	for _, p := range parts {
		p = strings.TrimSpace(p)
		if p != "" {
			out = append(out, p)
		}
	}
	return out
}

func usage() {
	fmt.Fprintf(os.Stderr, `node-image — dockerless Node.js OCI image builds

Usage:
  node-image build [dir] [flags]

Flags:
  --repo string        destination repository (required unless --no-push / --local)
  --base string        base image override
  --platform string    linux/amd64,linux/arm64
  -t string            tags (comma-separated)
  --skip-build         skip pnpm compile step
  --no-push            write local digest summary instead of pushing
  --local, -L          load into local Docker daemon (prints node-image.local/...@sha256:...)
  --oci-dir string     output dir for --no-push
  --empty-base         scratch base (tests)
  --max-layers int     max total layers including base (default 127)

Stdout prints exactly one line: the fully resolved image ref (repo@sha256:...),
so docker run --rm $(node-image build -L ...) works. Progress goes to stderr.

dir defaults to . and must contain package.json; pnpm-lock.yaml may be in a parent.
`)
}
