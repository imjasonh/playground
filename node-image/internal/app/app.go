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

// CollectOptions controls which files enter the app layer.
type CollectOptions struct {
	Include []string
	Exclude []string
}

// CollectOutputs returns files to place in the app layer under workdir prefix.
// When Include is set, only matching globs are packed (plus always-useful
// package.json if matched or explicitly listed). Otherwise prefer dist/ if it
// exists; else package.json + non-node_modules JS/JSON at root.
// Symlinks are rejected so a malicious build cannot pull host files into the image.
func CollectOutputs(dir string) (map[string]string, error) {
	return CollectOutputsOpts(dir, CollectOptions{})
}

// CollectOutputsOpts is CollectOutputs with include/exclude globs.
func CollectOutputsOpts(dir string, opt CollectOptions) (map[string]string, error) {
	if len(opt.Include) > 0 {
		return collectGlobs(dir, opt.Include, opt.Exclude)
	}
	out := map[string]string{}
	dist := filepath.Join(dir, "dist")
	if st, err := os.Lstat(dist); err == nil && st.IsDir() {
		if err := walkFiles(dir, dist, out, opt.Exclude); err != nil {
			return nil, err
		}
	}
	buildDir := filepath.Join(dir, "build")
	if st, err := os.Lstat(buildDir); err == nil && st.IsDir() {
		if err := walkFiles(dir, buildDir, out, opt.Exclude); err != nil {
			return nil, err
		}
	}
	for _, name := range []string{"package.json", "index.js", "index.mjs", "index.cjs"} {
		p := filepath.Join(dir, name)
		st, err := os.Lstat(p)
		if err != nil || st.IsDir() {
			continue
		}
		if st.Mode()&os.ModeSymlink != 0 {
			return nil, fmt.Errorf("refusing symlink in app outputs: %s", name)
		}
		if excluded(name, opt.Exclude) {
			continue
		}
		out[name] = p
	}
	if len(out) == 0 {
		return nil, fmt.Errorf("no app outputs found in %s\nHint: expected dist/ or build/ after compile, or an index.js / package.json at the package root. Set node-image.include globs, or pass --skip-build only after compiling yourself", dir)
	}
	return out, nil
}

func collectGlobs(dir string, include, exclude []string) (map[string]string, error) {
	out := map[string]string{}
	for _, pattern := range include {
		pattern = filepath.ToSlash(pattern)
		matches, err := filepath.Glob(filepath.Join(dir, filepath.FromSlash(pattern)))
		if err != nil {
			return nil, fmt.Errorf("include glob %q: %w", pattern, err)
		}
		// Also support ** by walking when pattern contains **.
		if strings.Contains(pattern, "**") {
			if err := walkGlob(dir, pattern, exclude, out); err != nil {
				return nil, err
			}
			continue
		}
		for _, m := range matches {
			st, err := os.Lstat(m)
			if err != nil {
				continue
			}
			if st.IsDir() {
				if err := walkFiles(dir, m, out, exclude); err != nil {
					return nil, err
				}
				continue
			}
			if st.Mode()&os.ModeSymlink != 0 {
				rel, _ := filepath.Rel(dir, m)
				return nil, fmt.Errorf("refusing symlink in app outputs: %s", filepath.ToSlash(rel))
			}
			rel, err := filepath.Rel(dir, m)
			if err != nil {
				return nil, err
			}
			rel = filepath.ToSlash(rel)
			if excluded(rel, exclude) {
				continue
			}
			out[rel] = m
		}
	}
	if len(out) == 0 {
		return nil, fmt.Errorf("no app outputs matched include globs %v in %s", include, dir)
	}
	return out, nil
}

func walkGlob(dir, pattern string, exclude []string, out map[string]string) error {
	// Convert simple "build/**" / "build/**/*.js" into a walk under the prefix.
	prefix := pattern
	if i := strings.Index(pattern, "**"); i >= 0 {
		prefix = strings.TrimSuffix(pattern[:i], "/")
	}
	root := dir
	if prefix != "" {
		root = filepath.Join(dir, filepath.FromSlash(prefix))
	}
	st, err := os.Lstat(root)
	if err != nil {
		if os.IsNotExist(err) {
			return nil
		}
		return err
	}
	if !st.IsDir() {
		rel, _ := filepath.Rel(dir, root)
		rel = filepath.ToSlash(rel)
		if matchDoublestar(pattern, rel) && !excluded(rel, exclude) {
			out[rel] = root
		}
		return nil
	}
	return filepath.Walk(root, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}
		if info.IsDir() {
			base := info.Name()
			if base == "node_modules" || base == ".git" {
				return filepath.SkipDir
			}
			return nil
		}
		if info.Mode()&os.ModeSymlink != 0 {
			rel, _ := filepath.Rel(dir, path)
			return fmt.Errorf("refusing symlink in app outputs: %s", filepath.ToSlash(rel))
		}
		rel, err := filepath.Rel(dir, path)
		if err != nil {
			return err
		}
		rel = filepath.ToSlash(rel)
		if !matchDoublestar(pattern, rel) || excluded(rel, exclude) {
			return nil
		}
		out[rel] = path
		return nil
	})
}

func matchDoublestar(pattern, rel string) bool {
	// filepath.Match does not support **; approximate:
	// "build/**" matches anything under build/
	// "build/**/*.lua" matches *.lua under build/
	if !strings.Contains(pattern, "**") {
		ok, _ := filepath.Match(pattern, rel)
		return ok
	}
	parts := strings.SplitN(pattern, "**", 2)
	prefix := strings.TrimSuffix(parts[0], "/")
	suffix := strings.TrimPrefix(parts[1], "/")
	if prefix != "" {
		if rel != prefix && !strings.HasPrefix(rel, prefix+"/") {
			return false
		}
	}
	if suffix == "" || suffix == "*" {
		return true
	}
	base := rel
	if prefix != "" {
		base = strings.TrimPrefix(rel, prefix+"/")
	}
	if strings.HasPrefix(suffix, "*.") || strings.HasPrefix(suffix, "*") {
		ok, _ := filepath.Match(suffix, filepath.Base(base))
		if ok {
			return true
		}
		ok, _ = filepath.Match(suffix, base)
		return ok
	}
	ok, _ := filepath.Match(suffix, base)
	return ok
}

func walkFiles(dir, root string, out map[string]string, exclude []string) error {
	return filepath.Walk(root, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}
		if info.IsDir() {
			if info.Name() == "node_modules" || info.Name() == ".git" {
				return filepath.SkipDir
			}
			return nil
		}
		if info.Mode()&os.ModeSymlink != 0 {
			rel, _ := filepath.Rel(dir, path)
			return fmt.Errorf("refusing symlink in app outputs: %s\nHint: build artifacts must be regular files", filepath.ToSlash(rel))
		}
		rel, _ := filepath.Rel(dir, path)
		rel = filepath.ToSlash(rel)
		if excluded(rel, exclude) {
			return nil
		}
		out[rel] = path
		return nil
	})
}

func excluded(rel string, patterns []string) bool {
	for _, p := range patterns {
		p = filepath.ToSlash(p)
		if ok, _ := filepath.Match(p, rel); ok {
			return true
		}
		if ok, _ := filepath.Match(p, filepath.Base(rel)); ok {
			return true
		}
		if strings.Contains(p, "**") && matchDoublestar(p, rel) {
			return true
		}
	}
	return false
}

// RequireMain ensures the configured package.json#main will exist in the image
// app layer. main is interpreted relative to the package directory.
func RequireMain(dir, main string, outputs map[string]string) error {
	if main == "" {
		return nil
	}
	if filepath.IsAbs(main) {
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
	return fmt.Errorf("package.json main %q is missing from app outputs\nHint: run the build so %s exists, set \"main\" / node-image.include so it is packed, or pass --skip-build only after compiling", main, rel)
}
