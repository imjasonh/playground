package layout

import (
	"bytes"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
)

// ApplyPatch applies a unified diff patch file to pkgDir (package root).
// Tries a minimal in-process applier first (fixture-friendly), then `patch -p1`
// when available (pnpm-compatible for complex patches).
func ApplyPatch(pkgDir, patchFile string) error {
	if patchFile == "" {
		return nil
	}
	st, err := os.Stat(patchFile)
	if err != nil {
		return fmt.Errorf("patch file: %w", err)
	}
	if st.IsDir() {
		return fmt.Errorf("patch path is a directory: %s", patchFile)
	}
	if err := applyPatchGo(pkgDir, patchFile); err == nil {
		return nil
	}
	goErr := err
	if _, err := exec.LookPath("patch"); err == nil {
		cmd := exec.Command("patch", "-p1", "--forward", "--batch", "-i", patchFile)
		cmd.Dir = pkgDir
		var stderr bytes.Buffer
		cmd.Stderr = &stderr
		cmd.Stdout = &stderr
		if err := cmd.Run(); err != nil {
			return fmt.Errorf("apply patch %s: go applier: %v; patch(1): %w\n%s", patchFile, goErr, err, stderr.String())
		}
		return nil
	}
	return fmt.Errorf("apply patch %s: %w", patchFile, goErr)
}

// applyPatchGo handles simple unified diffs that append lines (sufficient for
// fixtures and many pnpm patches that only add markers).
func applyPatchGo(pkgDir, patchFile string) error {
	b, err := os.ReadFile(patchFile)
	if err != nil {
		return err
	}
	lines := strings.Split(string(b), "\n")
	var target string
	var additions []string
	for _, line := range lines {
		if strings.HasPrefix(line, "+++ ") {
			target = strings.TrimSpace(strings.TrimPrefix(line, "+++ "))
			target = strings.TrimPrefix(target, "b/")
			if i := strings.IndexAny(target, "\t "); i >= 0 {
				target = target[:i]
			}
			continue
		}
		if strings.HasPrefix(line, "+") && !strings.HasPrefix(line, "+++") {
			additions = append(additions, strings.TrimPrefix(line, "+"))
		}
	}
	if target == "" || strings.Contains(target, "..") {
		return fmt.Errorf("could not parse patch target from %s", patchFile)
	}
	path := filepath.Join(pkgDir, filepath.FromSlash(target))
	if !isWithinDir(pkgDir, path) {
		return fmt.Errorf("patch target escapes package: %s", target)
	}
	existing, err := os.ReadFile(path)
	if err != nil {
		return err
	}
	// Idempotent: if all addition lines already present at end, succeed.
	content := string(existing)
	allPresent := true
	for _, a := range additions {
		if a == "" {
			continue
		}
		if !strings.Contains(content, a) {
			allPresent = false
			break
		}
	}
	if allPresent && len(additions) > 0 {
		return nil
	}
	var buf bytes.Buffer
	buf.Write(existing)
	if len(existing) > 0 && existing[len(existing)-1] != '\n' {
		buf.WriteByte('\n')
	}
	for _, a := range additions {
		buf.WriteString(a)
		buf.WriteByte('\n')
	}
	return os.WriteFile(path, buf.Bytes(), 0o644)
}
