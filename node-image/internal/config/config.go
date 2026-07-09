package config

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
)

// Config is build configuration from package.json + flags.
type Config struct {
	Dir        string
	Repo       string
	Base       string
	Platforms  []string
	Tags       []string
	SkipBuild  bool
	NoPush     bool
	OCIDir     string
	BuildScript string
	Entrypoint []string
	Main       string
	User       string
	Workdir    string
	MaxLayers  int
}

type packageJSON struct {
	Name    string            `json:"name"`
	Main    string            `json:"main"`
	Scripts map[string]string `json:"scripts"`
	NodeImage *nodeImageBlock `json:"node-image"`
}

type nodeImageBlock struct {
	Repo       string   `json:"repo"`
	Base       string   `json:"base"`
	Platforms  []string `json:"platforms"`
	Entrypoint []string `json:"entrypoint"`
	BuildScript string  `json:"buildScript"`
	User       string   `json:"user"`
	Workdir    string   `json:"workdir"`
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
	}
	if cfg.Main == "" {
		cfg.Main = "index.js"
	}
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
		if n.BuildScript != "" {
			cfg.BuildScript = n.BuildScript
		}
		if n.User != "" {
			cfg.User = n.User
		}
		if n.Workdir != "" {
			cfg.Workdir = n.Workdir
		}
	}
	if cfg.BuildScript == "" && pj.Scripts["build"] != "" {
		cfg.BuildScript = "build"
	}
	if len(cfg.Entrypoint) == 0 {
		cfg.Entrypoint = []string{"/nodejs/bin/node", filepath.ToSlash(filepath.Join(cfg.Workdir, cfg.Main))}
		// distroless node often uses node as entrypoint with cmd; keep simple:
		cfg.Entrypoint = []string{"/nodejs/bin/node"}
	}
	return cfg, &pj, nil
}

// Cmd returns the container Cmd (args to node).
func (c *Config) Cmd() []string {
	main := c.Main
	if !filepath.IsAbs(main) {
		main = filepath.ToSlash(filepath.Join(c.Workdir, main))
	}
	return []string{main}
}
