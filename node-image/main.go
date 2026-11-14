// Command node-image packs a pnpm-resolved production dependency graph into
// OCI layers.
package main

import (
	"context"
	"fmt"
	"log"
	"os"
	"strings"

	"github.com/spf13/cobra"

	"github.com/imjasonh/playground/node-image/internal/buildcmd"
	whbiab "github.com/imjasonh/playground/wehadababyitsaboy/go"
)

func main() {
	if err := whbiab.Execute(context.Background(), newRoot()); err != nil {
		log.Fatal("node-image:", err)
	}
}

func newRoot() *cobra.Command {
	root := &cobra.Command{
		Use:   "node-image",
		Short: "Pack a pnpm project into an OCI image",
		Long: `node-image packs a pnpm-resolved production dependency graph into OCI layers.
It does not replace pnpm: use pnpm (or turbo/esbuild/etc.) to install and
compile; use node-image to fetch hermetic prod deps and push an image.

dir defaults to . and must contain package.json; pnpm-lock.yaml may be in a parent.
Stdout of build prints exactly one image ref line.`,
		SilenceUsage:  true,
		SilenceErrors: true,
		Version:       "0.0.0-dev",
	}
	root.SetOut(os.Stdout)
	root.SetErr(os.Stderr)
	root.SetVersionTemplate("node-image {{.Version}}\n")

	var o buildOptions
	build := &cobra.Command{
		Use:   "build [dir]",
		Short: "Build and publish an image",
		Args:  cobra.MaximumNArgs(1),
		RunE: func(_ *cobra.Command, args []string) error {
			return runBuild(&o, args)
		},
	}
	f := build.Flags()
	f.StringVar(&o.repo, "repo", "", "destination repository (required unless --no-push)")
	f.StringVar(&o.base, "base", "", "base image (default from config / distroless node)")
	f.StringVar(&o.platform, "platform", "", "comma-separated platforms (default linux/amd64,linux/arm64)")
	f.StringVarP(&o.tag, "tag", "t", "", "comma-separated tags")
	f.BoolVar(&o.skipBuild, "skip-build", false, "skip pnpm run build; pack existing outputs (monorepo CI default)")
	f.BoolVar(&o.noPush, "no-push", false, "do not push; write digest summary instead")
	f.BoolVarP(&o.local, "local", "L", false, "load image into local Docker daemon instead of pushing")
	f.StringVar(&o.ociDir, "oci-dir", "", "output directory for --no-push digest summary")
	f.BoolVar(&o.emptyBase, "empty-base", false, "use scratch instead of pulling base (testing)")
	f.IntVar(&o.maxLayers, "max-layers", 0, "max total image layers including base (default 127)")
	f.StringVar(&o.command, "command", "", "named command from node-image.commands")
	f.StringVar(&o.allowScripts, "allow-scripts", "", "comma-separated package names allowed to need native builds (scripts still not run)")
	f.StringVar(&o.cacheDir, "cache-dir", "", "content-addressed cache root (packages/spool/layers)")
	f.StringVar(&o.entrypoint, "entrypoint", "", "comma-separated entrypoint override")

	diagnose := &cobra.Command{
		Use:   "diagnose [dir]",
		Short: "Explain why a directory cannot be packed",
		Args:  cobra.MaximumNArgs(1),
		RunE: func(_ *cobra.Command, args []string) error {
			dir := "."
			if len(args) == 1 {
				dir = args[0]
			}
			return buildcmd.Diagnose(dir, os.Stderr)
		},
	}

	version := &cobra.Command{
		Use:   "version",
		Short: "Print the version",
		Args:  cobra.NoArgs,
		Run: func(cmd *cobra.Command, _ []string) {
			fmt.Fprintln(cmd.OutOrStdout(), "node-image "+cmd.Root().Version)
		},
	}

	root.AddCommand(build, diagnose, version)
	return root
}

// buildOptions holds the flags of `node-image build`.
type buildOptions struct {
	repo, base, platform, tag string
	skipBuild, noPush, local  bool
	ociDir                    string
	emptyBase                 bool
	maxLayers                 int
	command, allowScripts     string
	cacheDir, entrypoint      string
}

func runBuild(o *buildOptions, args []string) error {
	dir := "."
	if len(args) == 1 {
		dir = args[0]
	}
	var platforms []string
	if o.platform != "" {
		platforms = splitCSV(o.platform)
	}
	var tags []string
	if o.tag != "" {
		tags = splitCSV(o.tag)
	}
	_, err := buildcmd.Run(buildcmd.Options{
		Dir:          dir,
		Repo:         o.repo,
		Base:         o.base,
		Platforms:    platforms,
		Tags:         tags,
		SkipBuild:    o.skipBuild,
		NoPush:       o.noPush,
		Local:        o.local,
		OCIDir:       o.ociDir,
		EmptyBase:    o.emptyBase,
		MaxLayers:    o.maxLayers,
		Command:      o.command,
		AllowScripts: splitCSV(o.allowScripts),
		CacheDir:     o.cacheDir,
		Entrypoint:   splitCSV(o.entrypoint),
	})
	return err
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
