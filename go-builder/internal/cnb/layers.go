package cnb

import (
	"fmt"
	"os"
	"path/filepath"
	"sort"
	"strings"
)

// LayerTypes controls whether a layer is available at launch/build and cached.
type LayerTypes struct {
	Launch bool
	Build  bool
	Cache  bool
}

// Layer is a CNB layer directory plus its sidecar .toml metadata.
type Layer struct {
	Name string
	Path string
	Toml string
}

// CreateLayer makes layers_dir/name and returns paths for the dir and toml.
func CreateLayer(layersDir, name string) (Layer, error) {
	if err := validateLayerName(name); err != nil {
		return Layer{}, err
	}
	path := filepath.Join(layersDir, name)
	if err := os.MkdirAll(path, 0o755); err != nil {
		return Layer{}, err
	}
	return Layer{
		Name: name,
		Path: path,
		Toml: filepath.Join(layersDir, name+".toml"),
	}, nil
}

// WriteLayerTOML writes the types (+ optional metadata) sidecar for a layer.
func WriteLayerTOML(layer Layer, types LayerTypes, metadata map[string]string) error {
	var b strings.Builder
	b.WriteString("[types]\n")
	fmt.Fprintf(&b, "launch = %t\n", types.Launch)
	fmt.Fprintf(&b, "build = %t\n", types.Build)
	fmt.Fprintf(&b, "cache = %t\n", types.Cache)
	if len(metadata) > 0 {
		b.WriteString("\n[metadata]\n")
		// Stable order for determinism in tests.
		keys := make([]string, 0, len(metadata))
		for k := range metadata {
			keys = append(keys, k)
		}
		sortStrings(keys)
		for _, k := range keys {
			fmt.Fprintf(&b, "%s = %q\n", k, metadata[k])
		}
	}
	return os.WriteFile(layer.Toml, []byte(b.String()), 0o644)
}

// ReadLayerMetadata parses simple key = "value" entries under [metadata].
func ReadLayerMetadata(tomlPath string) (map[string]string, error) {
	b, err := os.ReadFile(tomlPath)
	if err != nil {
		if os.IsNotExist(err) {
			return nil, nil
		}
		return nil, err
	}
	out := map[string]string{}
	inMeta := false
	for _, line := range strings.Split(string(b), "\n") {
		line = strings.TrimSpace(line)
		if line == "" || strings.HasPrefix(line, "#") {
			continue
		}
		if strings.HasPrefix(line, "[") {
			inMeta = line == "[metadata]"
			continue
		}
		if !inMeta {
			continue
		}
		k, v, ok := strings.Cut(line, "=")
		if !ok {
			continue
		}
		k = strings.TrimSpace(k)
		v = strings.TrimSpace(v)
		v = strings.Trim(v, `"`)
		out[k] = v
	}
	return out, nil
}

// Process is a CNB launch process.
type Process struct {
	Type    string
	Command []string
	Default bool
	// WorkingDirectory is optional; empty means app dir.
	WorkingDirectory string
}

// WriteLaunchTOML writes layers_dir/launch.toml with the given processes.
// Process environment (e.g. KO_DATA_PATH) belongs in a launch layer's env/
// directory via WriteLayerEnv — the env argument is reserved for callers that
// want to assert what they configured; it is not written here.
func WriteLaunchTOML(layersDir string, processes []Process, _ map[string]string) error {
	var b strings.Builder
	for _, p := range processes {
		b.WriteString("[[processes]]\n")
		fmt.Fprintf(&b, "type = %q\n", p.Type)
		b.WriteString("command = [")
		for i, c := range p.Command {
			if i > 0 {
				b.WriteString(", ")
			}
			fmt.Fprintf(&b, "%q", c)
		}
		b.WriteString("]\n")
		if p.Default {
			b.WriteString("default = true\n")
		}
		if p.WorkingDirectory != "" {
			fmt.Fprintf(&b, "working-directory = %q\n", p.WorkingDirectory)
		}
		b.WriteString("\n")
	}
	return os.WriteFile(filepath.Join(layersDir, "launch.toml"), []byte(b.String()), 0o644)
}

// WriteLayerEnv writes layer/env/KEY(.default|.override|.append|/prepend) files.
func WriteLayerEnv(layerPath, key, value, suffix string) error {
	dir := filepath.Join(layerPath, "env")
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return err
	}
	name := key
	if suffix != "" {
		name = key + "." + suffix
	}
	return os.WriteFile(filepath.Join(dir, name), []byte(value), 0o644)
}

func validateLayerName(name string) error {
	if name == "" || strings.Contains(name, "/") || strings.Contains(name, `\`) {
		return fmt.Errorf("invalid layer name %q", name)
	}
	return nil
}

func sortStrings(s []string) { sort.Strings(s) }
