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
	Dir         string
	Repo        string
	Base        string
	Platforms   []string
	Tags        []string
	SkipBuild   bool
	NoPush      bool
	Local       bool
	OCIDir      string
	BuildScript string
	Entrypoint  []string
	CmdOverride []string // explicit node-image.cmd, if set
	Main        string
	User        string
	Workdir     string
	MaxLayers   int
	Env         map[string]string
	EnginesNode string // package.json engines.node, if set
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
	Repo        string            `json:"repo"`
	Base        string            `json:"base"`
	Platforms   []string          `json:"platforms"`
	Entrypoint  []string          `json:"entrypoint"`
	Cmd         []string          `json:"cmd"`
	Main        string            `json:"main"`
	BuildScript string            `json:"buildScript"`
	User        string            `json:"user"`
	Workdir     string            `json:"workdir"`
	MaxLayers   int               `json:"maxLayers"`
	Env         map[string]string `json:"env"`
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
	}
	if cfg.BuildScript == "" && pj.Scripts["build"] != "" {
		cfg.BuildScript = "build"
	}
	if len(cfg.Entrypoint) == 0 {
		// Distroless node images typically ship node at /nodejs/bin/node.
		cfg.Entrypoint = []string{"/nodejs/bin/node"}
	}
	// Main is resolved after compile (see ResolveMain) — dist/ often does not
	// exist yet when Load runs.
	return cfg, &pj, nil
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
				base+".js",
			)
		}
	}
	candidates = append(candidates,
		"dist/index.js",
		"dist/index.mjs",
		"dist/main.js",
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
			// Never run .ts in the image.
			continue
		}
		if st, err := os.Stat(filepath.Join(dir, filepath.FromSlash(c))); err == nil && !st.IsDir() {
			return c, nil
		}
	}

	if hasBuildScript {
		return "", fmt.Errorf("could not find a compiled JS entrypoint (looked for dist/index.js and friends)\nHint: package.json main is %q; after `pnpm run build` set node-image.main to the emitted file (e.g. \"dist/index.js\"), or ensure the build writes dist/index.js", main)
	}
	if firstMissingTS != "" {
		return "", fmt.Errorf("package.json main %q looks like TypeScript but no scripts.build is configured and no compiled JS was found\nHint: add a build script that emits JS to dist/, set \"node-image\".\"main\" to that file, or use a JS entrypoint", firstMissingTS)
	}
	if main != "" {
		return main, nil // let RequireMain fail later with a clearer missing-file error
	}
	return "index.js", nil
}

// Cmd returns the container Cmd (args to node).
func (c *Config) Cmd() []string {
	if len(c.CmdOverride) > 0 {
		return append([]string(nil), c.CmdOverride...)
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
	// stable order
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

func copyEnv(in map[string]string) map[string]string {
	out := make(map[string]string, len(in)+1)
	for k, v := range in {
		out[k] = v
	}
	return out
}
