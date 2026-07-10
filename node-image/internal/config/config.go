package config

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"strings"
)

// Config is build configuration from package.json + flags.
type Config struct {
	Dir          string
	Repo         string
	Base         string
	Platforms    []string
	Tags         []string
	SkipBuild    bool
	NoPush       bool
	Local        bool
	OCIDir       string
	BuildScript  string
	Entrypoint   []string
	CmdOverride  []string // explicit node-image.cmd, if set
	Main         string
	User         string
	Workdir      string
	MaxLayers    int
	Env          map[string]string
	EnginesNode  string // package.json engines.node, if set
	Include      []string
	Exclude      []string
	Commands     map[string][]string
	CommandName  string // selected named command (from --command)
	AllowScripts []string
	Unbucketed   []string
	CacheDir     string
}

type packageJSON struct {
	Name      string            `json:"name"`
	Main      string            `json:"main"`
	Scripts   map[string]string `json:"scripts"`
	Engines   map[string]string `json:"engines"`
	NodeImage *nodeImageBlock   `json:"node-image"`
}

// EnginesNode returns package.json engines.node if set.
func (p *packageJSON) EnginesNode() string {
	if p == nil || p.Engines == nil {
		return ""
	}
	return p.Engines["node"]
}

type nodeImageBlock struct {
	Repo         string              `json:"repo"`
	Base         string              `json:"base"`
	Platforms    []string            `json:"platforms"`
	Entrypoint   []string            `json:"entrypoint"`
	Cmd          []string            `json:"cmd"`
	Main         string              `json:"main"`
	BuildScript  string              `json:"buildScript"`
	SkipBuild    *bool               `json:"skipBuild"`
	User         string              `json:"user"`
	Workdir      string              `json:"workdir"`
	MaxLayers    int                 `json:"maxLayers"`
	Env          map[string]string   `json:"env"`
	Include      []string            `json:"include"`
	Exclude      []string            `json:"exclude"`
	Commands     map[string][]string `json:"commands"`
	AllowScripts []string            `json:"allowScripts"`
	Unbucketed   []string            `json:"unbucketed"`
}

// DefaultBase is a glibc distroless Node image.
const DefaultBase = "gcr.io/distroless/nodejs22-debian12"

// Load reads package.json from dir and applies defaults.
func Load(dir string) (*Config, *packageJSON, error) {
	abs, err := filepath.Abs(dir)
	if err != nil {
		return nil, nil, err
	}
	b, err := os.ReadFile(filepath.Join(abs, "package.json"))
	if err != nil {
		return nil, nil, fmt.Errorf("package.json required in %s: %w", abs, err)
	}
	var pj packageJSON
	if err := json.Unmarshal(b, &pj); err != nil {
		return nil, nil, err
	}
	cfg := &Config{
		Dir:       abs,
		Base:      DefaultBase,
		Platforms: []string{"linux/amd64", "linux/arm64"},
		Workdir:   "/app",
		User:      "65532",
		MaxLayers: 127,
		Main:      pj.Main,
		Env:       map[string]string{"NODE_ENV": "production"},
	}
	cfg.EnginesNode = pj.EnginesNode()
	if pj.NodeImage != nil {
		n := pj.NodeImage
		if n.Repo != "" {
			cfg.Repo = n.Repo
		}
		if n.Base != "" {
			cfg.Base = n.Base
		}
		if len(n.Platforms) > 0 {
			cfg.Platforms = n.Platforms
		}
		if len(n.Entrypoint) > 0 {
			cfg.Entrypoint = n.Entrypoint
		}
		if len(n.Cmd) > 0 {
			cfg.CmdOverride = append([]string(nil), n.Cmd...)
		}
		if n.Main != "" {
			cfg.Main = n.Main
		}
		if n.BuildScript != "" {
			cfg.BuildScript = n.BuildScript
		}
		if n.SkipBuild != nil && *n.SkipBuild {
			cfg.SkipBuild = true
		}
		if n.User != "" {
			cfg.User = n.User
		}
		if n.Workdir != "" {
			cfg.Workdir = n.Workdir
		}
		if n.MaxLayers > 0 {
			cfg.MaxLayers = n.MaxLayers
		}
		if len(n.Env) > 0 {
			for k, v := range n.Env {
				cfg.Env[k] = v
			}
		}
		if len(n.Include) > 0 {
			cfg.Include = append([]string(nil), n.Include...)
		}
		if len(n.Exclude) > 0 {
			cfg.Exclude = append([]string(nil), n.Exclude...)
		}
		if len(n.Commands) > 0 {
			cfg.Commands = n.Commands
		}
		if len(n.AllowScripts) > 0 {
			cfg.AllowScripts = append([]string(nil), n.AllowScripts...)
		}
		if len(n.Unbucketed) > 0 {
			cfg.Unbucketed = append([]string(nil), n.Unbucketed...)
		}
	}
	if cfg.BuildScript == "" && pj.Scripts["build"] != "" {
		cfg.BuildScript = "build"
	}
	if len(cfg.Entrypoint) == 0 {
		// Distroless node images typically ship node at /nodejs/bin/node.
		// Custom bases should set node-image.entrypoint (e.g. ["node"]).
		cfg.Entrypoint = []string{"/nodejs/bin/node"}
	}
	return cfg, &pj, nil
}

// ApplyCommand selects a named command from node-image.commands into CmdOverride.
func (c *Config) ApplyCommand(name string) error {
	if name == "" {
		return nil
	}
	if c.Commands == nil {
		return fmt.Errorf("unknown --command %q (no node-image.commands configured)", name)
	}
	cmd, ok := c.Commands[name]
	if !ok {
		keys := make([]string, 0, len(c.Commands))
		for k := range c.Commands {
			keys = append(keys, k)
		}
		return fmt.Errorf("unknown --command %q (have: %s)", name, strings.Join(keys, ", "))
	}
	c.CommandName = name
	c.CmdOverride = append([]string(nil), cmd...)
	return nil
}

// ResolveMain picks the JS file node should run.
//
// package.json#main is often a TypeScript source path in real apps (e.g.
// "index.ts" or "src/index.ts") even when scripts.build emits dist/. Prefer
// an existing compiled artifact over a .ts main when a build script exists.
func ResolveMain(dir, main string, hasBuildScript bool) (string, error) {
	candidates := []string{}
	if main != "" {
		candidates = append(candidates, main)
		if strings.HasSuffix(main, ".ts") {
			base := strings.TrimSuffix(main, ".ts")
			candidates = append(candidates,
				filepath.ToSlash(filepath.Join("dist", filepath.Base(base)+".js")),
				filepath.ToSlash(filepath.Join("dist", base+".js")),
				filepath.ToSlash(filepath.Join("build", filepath.Base(base)+".js")),
				base+".js",
			)
		}
	}
	candidates = append(candidates,
		"dist/index.js",
		"dist/index.mjs",
		"dist/main.js",
		"build/index.js",
		"build/index.mjs",
		"index.js",
		"index.mjs",
		"index.cjs",
	)

	seen := map[string]struct{}{}
	var firstMissingTS string
	for _, c := range candidates {
		c = filepath.ToSlash(strings.TrimPrefix(c, "./"))
		if c == "" {
			continue
		}
		if _, ok := seen[c]; ok {
			continue
		}
		seen[c] = struct{}{}
		if strings.HasSuffix(c, ".ts") {
			if firstMissingTS == "" {
				firstMissingTS = c
			}
			continue
		}
		if st, err := os.Stat(filepath.Join(dir, filepath.FromSlash(c))); err == nil && !st.IsDir() {
			return c, nil
		}
	}

	if hasBuildScript {
		return "", fmt.Errorf("could not find a compiled JS entrypoint (looked for dist/index.js, build/index.js, and friends)\nHint: package.json main is %q; after compile set node-image.main to the emitted file, or set node-image.include", main)
	}
	if firstMissingTS != "" {
		return "", fmt.Errorf("package.json main %q looks like TypeScript but no scripts.build is configured and no compiled JS was found\nHint: add a build script that emits JS, set \"node-image\".\"main\" to that file, use --skip-build after compiling externally, or use a JS entrypoint", firstMissingTS)
	}
	if main != "" {
		return main, nil
	}
	return "index.js", nil
}

// Cmd returns the container Cmd (args to node).
func (c *Config) Cmd() []string {
	if len(c.CmdOverride) > 0 {
		out := make([]string, len(c.CmdOverride))
		for i, a := range c.CmdOverride {
			if !filepath.IsAbs(a) && !strings.HasPrefix(a, "/") {
				out[i] = filepath.ToSlash(filepath.Join(c.Workdir, a))
			} else {
				out[i] = a
			}
		}
		return out
	}
	main := c.Main
	if !filepath.IsAbs(main) {
		main = filepath.ToSlash(filepath.Join(c.Workdir, main))
	}
	return []string{main}
}

// EnvList returns OCI config Env entries (KEY=VAL), with NODE_ENV defaulting
// to production unless overridden via node-image.env.
func (c *Config) EnvList() []string {
	env := c.Env
	if env == nil {
		env = map[string]string{"NODE_ENV": "production"}
	}
	if _, ok := env["NODE_ENV"]; !ok {
		env = copyEnv(env)
		env["NODE_ENV"] = "production"
	}
	keys := make([]string, 0, len(env))
	for k := range env {
		keys = append(keys, k)
	}
	for i := 0; i < len(keys); i++ {
		for j := i + 1; j < len(keys); j++ {
			if keys[j] < keys[i] {
				keys[i], keys[j] = keys[j], keys[i]
			}
		}
	}
	out := make([]string, 0, len(keys))
	for _, k := range keys {
		out = append(out, k+"="+env[k])
	}
	return out
}

// AllowsScript reports whether packageName is on the allowScripts list.
func (c *Config) AllowsScript(packageName string) bool {
	for _, a := range c.AllowScripts {
		name := a
		if i := strings.Index(a, "@"); i > 0 && !strings.HasPrefix(a, "@") {
			name = a[:i]
		} else if strings.HasPrefix(a, "@") {
			// @scope/name or @scope/name@1.0.0
			rest := a[1:]
			if j := strings.Index(rest, "@"); j > 0 {
				name = "@" + rest[:j]
			}
		}
		if name == packageName || a == packageName {
			return true
		}
	}
	return false
}

func copyEnv(in map[string]string) map[string]string {
	out := make(map[string]string, len(in)+1)
	for k, v := range in {
		out[k] = v
	}
	return out
}
