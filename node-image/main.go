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
	case "diagnose":
		dir := "."
		if len(os.Args) > 2 {
			dir = os.Args[2]
		}
		if err := buildcmd.Diagnose(dir, os.Stderr); err != nil {
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
	skipBuild := fs.Bool("skip-build", false, "skip pnpm run build; pack existing outputs (monorepo CI default)")
	noPush := fs.Bool("no-push", false, "do not push; write digest summary instead")
	local := fs.Bool("local", false, "load image into local Docker daemon instead of pushing")
	fs.BoolVar(local, "L", false, "shorthand for --local")
	ociDir := fs.String("oci-dir", "", "output directory for --no-push digest summary")
	emptyBase := fs.Bool("empty-base", false, "use scratch instead of pulling base (testing)")
	maxLayers := fs.Int("max-layers", 0, "max total image layers including base (default 127)")
	command := fs.String("command", "", "named command from node-image.commands")
	allowScripts := fs.String("allow-scripts", "", "comma-separated package names allowed to need native builds (scripts still not run)")
	cacheDir := fs.String("cache-dir", "", "content-addressed cache root (packages/spool/layers)")
	entrypoint := fs.String("entrypoint", "", "comma-separated entrypoint override")
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
		Dir:          dir,
		Repo:         *repo,
		Base:         *base,
		Platforms:    platforms,
		Tags:         tags,
		SkipBuild:    *skipBuild,
		NoPush:       *noPush,
		Local:        *local,
		OCIDir:       *ociDir,
		EmptyBase:    *emptyBase,
		MaxLayers:    *maxLayers,
		Command:      *command,
		AllowScripts: splitCSV(*allowScripts),
		CacheDir:     *cacheDir,
		Entrypoint:   splitCSV(*entrypoint),
	})
	return err
}

func splitDirAndFlags(args []string) (dir string, flagArgs []string) {
	dir = "."
	if len(args) == 0 {
		return dir, nil
	}
	if !strings.HasPrefix(args[0], "-") {
		return args[0], args[1:]
	}
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
	fmt.Fprintf(os.Stderr, `node-image — dockerless Node.js OCI packaging (complementary to pnpm)

node-image packs a pnpm-resolved production dependency graph into OCI layers.
It does not replace pnpm: use pnpm (or turbo/esbuild/etc.) to install and
compile; use node-image to fetch hermetic prod deps and push an image.

Usage:
  node-image build [dir] [flags]
  node-image diagnose [dir]

Flags:
  --repo string          destination repository (required unless --no-push / --local)
  --base string          base image override
  --platform string      linux/amd64,linux/arm64
  -t string              tags (comma-separated)
  --skip-build           skip pnpm compile; pack existing outputs (monorepo CI default)
  --command string       named Cmd from package.json#node-image.commands
  --allow-scripts list   named packages allowed to need natives (scripts still not run)
  --cache-dir string     portable cache root for CI restore
  --entrypoint list      override image entrypoint (e.g. node)
  --no-push              write local digest summary instead of pushing
  --local, -L            load into local Docker daemon
  --oci-dir string       output dir for --no-push
  --empty-base           scratch base (tests)
  --max-layers int       max total layers including base (default 127)

Config: package.json "node-image" block (entrypoint, cmd, include/exclude, …);
flags override. Stdout prints exactly one image ref line.

dir defaults to . and must contain package.json; pnpm-lock.yaml may be in a parent.
`)
}
