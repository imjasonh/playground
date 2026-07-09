package app

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
)

// Compile runs pnpm install + pnpm run <script> in dir when script is non-empty.
func Compile(dir, lockRoot, script string) error {
	if script == "" {
		return nil
	}
	pnpm, err := exec.LookPath("pnpm")
	if err != nil {
		return fmt.Errorf("scripts.%s is set but pnpm is not on PATH\nHint: install pnpm (https://pnpm.io/installation) or corepack enable, or pass --skip-build if outputs are already compiled", script)
	}
	install := exec.Command(pnpm, "install", "--frozen-lockfile")
	install.Dir = lockRoot
	install.Stdout = os.Stderr
	install.Stderr = os.Stderr
	if err := install.Run(); err != nil {
		return fmt.Errorf("pnpm install: %w", err)
	}
	run := exec.Command(pnpm, "run", script)
	run.Dir = dir
	run.Stdout = os.Stderr
	run.Stderr = os.Stderr
	if err := run.Run(); err != nil {
		return fmt.Errorf("pnpm run %s: %w", script, err)
	}
	return nil
}

// CollectOutputs returns files to place in the app layer under workdir prefix.
// Prefer dist/ if it exists; otherwise package.json + non-node_modules JS/JSON at root.
func CollectOutputs(dir string) (map[string]string, error) {
	// map relative path → absolute source path
	out := map[string]string{}
	dist := filepath.Join(dir, "dist")
	if st, err := os.Stat(dist); err == nil && st.IsDir() {
		err := filepath.Walk(dist, func(path string, info os.FileInfo, err error) error {
			if err != nil || info.IsDir() {
				return err
			}
			rel, _ := filepath.Rel(dir, path)
			out[filepath.ToSlash(rel)] = path
			return nil
		})
		if err != nil {
			return nil, err
		}
	}
	for _, name := range []string{"package.json", "index.js", "index.mjs", "index.cjs"} {
		p := filepath.Join(dir, name)
		if st, err := os.Stat(p); err == nil && !st.IsDir() {
			out[name] = p
		}
	}
	if len(out) == 0 {
		return nil, fmt.Errorf("no app outputs found in %s\nHint: expected dist/ after `pnpm run build`, or an index.js / package.json at the package root. For TypeScript apps ensure scripts.build writes to dist/, or pass --skip-build only after compiling yourself", dir)
	}
	return out, nil
}

// RequireMain ensures the configured package.json#main will exist in the image
// app layer. main is interpreted relative to the package directory.
func RequireMain(dir, main string, outputs map[string]string) error {
	if main == "" {
		return nil
	}
	if filepath.IsAbs(main) {
		// Absolute container paths are the caller's responsibility.
		return nil
	}
	rel := filepath.ToSlash(filepath.Clean(main))
	rel = strings.TrimPrefix(rel, "./")
	if _, ok := outputs[rel]; ok {
		return nil
	}
	if st, err := os.Stat(filepath.Join(dir, filepath.FromSlash(rel))); err == nil && !st.IsDir() {
		return nil
	}
	return fmt.Errorf("package.json main %q is missing from app outputs\nHint: run the build so %s exists, set \"main\" to a file under dist/ or index.js, or pass --skip-build only after compiling", main, rel)
}
