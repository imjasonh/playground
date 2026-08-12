// Package config loads ko-compatible build configuration from .ko.yaml and
// buildpack / platform environment variables.
package config

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"

	"gopkg.in/yaml.v3"
)

// StringArray unmarshals either a string or a list of strings (ko/goreleaser).
type StringArray []string

func (a *StringArray) UnmarshalYAML(value *yaml.Node) error {
	switch value.Kind {
	case yaml.ScalarNode:
		var s string
		if err := value.Decode(&s); err != nil {
			return err
		}
		*a = []string{s}
		return nil
	case yaml.SequenceNode:
		var ss []string
		if err := value.Decode(&ss); err != nil {
			return err
		}
		*a = ss
		return nil
	default:
		return fmt.Errorf("ldflags: expected string or sequence, got kind %v", value.Kind)
	}
}

// FlagArray unmarshals a string (shell-split) or a list of strings.
type FlagArray []string

func (a *FlagArray) UnmarshalYAML(value *yaml.Node) error {
	switch value.Kind {
	case yaml.ScalarNode:
		var s string
		if err := value.Decode(&s); err != nil {
			return err
		}
		*a = strings.Fields(s)
		return nil
	case yaml.SequenceNode:
		var ss []string
		if err := value.Decode(&ss); err != nil {
			return err
		}
		*a = ss
		return nil
	default:
		return fmt.Errorf("flags: expected string or sequence, got kind %v", value.Kind)
	}
}

// Build is one entry under .ko.yaml's builds: list (GoReleaser-shaped).
type Build struct {
	ID      string      `yaml:"id,omitempty"`
	Dir     string      `yaml:"dir,omitempty"`
	Main    string      `yaml:"main,omitempty"`
	Ldflags StringArray `yaml:"ldflags,omitempty"`
	Flags   FlagArray   `yaml:"flags,omitempty"`
	Env     []string    `yaml:"env,omitempty"`
}

// File is the subset of .ko.yaml we honor.
type File struct {
	DefaultBaseImage string  `yaml:"defaultBaseImage,omitempty"`
	Builds           []Build `yaml:"builds,omitempty"`
	// Default* apply when a build entry omits the field.
	DefaultLdflags StringArray `yaml:"defaultLdflags,omitempty"`
	DefaultFlags   FlagArray   `yaml:"defaultFlags,omitempty"`
	DefaultEnv     []string    `yaml:"defaultEnv,omitempty"`
}

// Effective is the resolved build configuration for one image.
type Effective struct {
	// Main is the package import path or relative package (e.g. "." or "./cmd/app").
	Main string
	// Dir is the working directory for go build, relative to app root.
	Dir string
	// Flags are go build flags (excluding ldflags).
	Flags []string
	// Ldflags are passed as -ldflags=...
	Ldflags []string
	// Env are KEY=VALUE pairs for the build.
	Env []string
	// Trimpath mirrors ko's default of -trimpath.
	Trimpath bool
	// CGOEnabled defaults to "0" like ko.
	CGOEnabled string
	// DefaultBaseImage from .ko.yaml (informational — builder run image wins).
	DefaultBaseImage string
	// DisableOptimizations adds -gcflags=all=-N -l (ko --disable-optimizations).
	DisableOptimizations bool
}

// Load reads .ko.yaml from appDir (if present) and overlays platform/buildpack env.
func Load(appDir string, platformEnv map[string]string) (Effective, error) {
	eff := Effective{
		Main:       ".",
		Trimpath:   true,
		CGOEnabled: "0",
		Ldflags:    []string{"-s", "-w"},
	}

	koPath := filepath.Join(appDir, ".ko.yaml")
	if b, err := os.ReadFile(koPath); err == nil {
		var f File
		if err := yaml.Unmarshal(b, &f); err != nil {
			return Effective{}, fmt.Errorf("parse %s: %w", koPath, err)
		}
		eff.DefaultBaseImage = f.DefaultBaseImage
		if len(f.DefaultLdflags) > 0 {
			eff.Ldflags = append([]string{}, f.DefaultLdflags...)
		}
		if len(f.DefaultFlags) > 0 {
			eff.Flags = append([]string{}, f.DefaultFlags...)
		}
		if len(f.DefaultEnv) > 0 {
			eff.Env = append([]string{}, f.DefaultEnv...)
		}
		if len(f.Builds) > 0 {
			build := selectBuild(f.Builds, platformEnv)
			if build.Main != "" {
				eff.Main = build.Main
			}
			if build.Dir != "" {
				eff.Dir = build.Dir
			}
			if len(build.Ldflags) > 0 {
				eff.Ldflags = append([]string{}, build.Ldflags...)
			}
			if len(build.Flags) > 0 {
				eff.Flags = append([]string{}, build.Flags...)
			}
			if len(build.Env) > 0 {
				eff.Env = mergeEnv(eff.Env, build.Env)
			}
		}
	} else if !os.IsNotExist(err) {
		return Effective{}, err
	}

	// Platform / buildpack env overrides (BP_* and a few KO_* aliases).
	if v := firstEnv(platformEnv, "BP_GO_TARGETS", "KO_MAIN"); v != "" {
		// BP_GO_TARGETS can be space-separated; take the first like a single-image builder.
		eff.Main = strings.Fields(v)[0]
	}
	if v := firstEnv(platformEnv, "BP_GO_BUILD_FLAGS"); v != "" {
		eff.Flags = strings.Fields(v)
	}
	if v := firstEnv(platformEnv, "BP_GO_LDFLAGS", "KO_LDFLAGS"); v != "" {
		eff.Ldflags = []string{v}
	}
	if v := firstEnv(platformEnv, "CGO_ENABLED"); v != "" {
		eff.CGOEnabled = v
	}
	if v := firstEnv(platformEnv, "BP_GO_DISABLE_OPTIMIZATIONS", "KO_DISABLE_OPTIMIZATIONS"); v == "true" || v == "1" {
		eff.DisableOptimizations = true
	}
	if v := firstEnv(platformEnv, "BP_KEEP_FILES"); v != "" {
		// ignored — reserved for future; kodata is always kept
		_ = v
	}
	if v := firstEnv(platformEnv, "BP_GO_TRIMPATH"); v == "false" || v == "0" {
		eff.Trimpath = false
	}

	// Strip trailing .go filenames from Main the way ko does (package only).
	if strings.HasSuffix(eff.Main, ".go") {
		eff.Main = filepath.Dir(eff.Main)
		if eff.Main == "" {
			eff.Main = "."
		}
	}
	return eff, nil
}

func selectBuild(builds []Build, platformEnv map[string]string) Build {
	want := firstEnv(platformEnv, "BP_KO_BUILD_ID", "KO_BUILD_ID")
	if want != "" {
		for _, b := range builds {
			if b.ID == want {
				return b
			}
		}
	}
	return builds[0]
}

func firstEnv(env map[string]string, keys ...string) string {
	for _, k := range keys {
		if v, ok := env[k]; ok && v != "" {
			return v
		}
		// Also honor process environment for local `pack build --env`.
		if v := os.Getenv(k); v != "" {
			return v
		}
	}
	return ""
}

func mergeEnv(base, over []string) []string {
	seen := map[string]string{}
	order := make([]string, 0, len(base)+len(over))
	add := func(e string) {
		k, v, ok := strings.Cut(e, "=")
		if !ok {
			return
		}
		if _, exists := seen[k]; !exists {
			order = append(order, k)
		}
		seen[k] = v
	}
	for _, e := range base {
		add(e)
	}
	for _, e := range over {
		add(e)
	}
	out := make([]string, 0, len(order))
	for _, k := range order {
		out = append(out, k+"="+seen[k])
	}
	return out
}
