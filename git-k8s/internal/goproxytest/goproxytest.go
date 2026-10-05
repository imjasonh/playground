// Package goproxytest writes versions of Go modules in the layout that a
// module proxy serves, for tests.
package goproxytest

import (
	"encoding/json"
	"errors"
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"time"

	"golang.org/x/mod/modfile"
	"golang.org/x/mod/module"
	"golang.org/x/mod/semver"
	"golang.org/x/mod/zip"
)

// Publish adds a version of the module in dir, which holds the module's
// go.mod and other files, to root, a directory that a module proxy serves.
// The proxy reports t as the version's time.
func Publish(root, dir, version string, t time.Time) error {
	if semver.Canonical(version) != version || version == "" {
		return fmt.Errorf("%q isn't a canonical semantic version", version)
	}
	mod, err := os.ReadFile(filepath.Join(dir, "go.mod"))
	if err != nil {
		return err
	}
	path := modfile.ModulePath(mod)
	if path == "" {
		return fmt.Errorf("%s/go.mod has no module line", dir)
	}
	escPath, err := module.EscapePath(path)
	if err != nil {
		return err
	}
	escVersion, err := module.EscapeVersion(version)
	if err != nil {
		return err
	}
	versions := filepath.Join(root, filepath.FromSlash(escPath), "@v")
	if err := os.MkdirAll(versions, 0o755); err != nil {
		return err
	}
	f, err := os.Create(filepath.Join(versions, escVersion+".zip"))
	if err != nil {
		return err
	}
	if err := zip.CreateFromDir(f, module.Version{Path: path, Version: version}, dir); err != nil {
		f.Close()
		return err
	}
	if err := f.Close(); err != nil {
		return err
	}
	if err := os.WriteFile(filepath.Join(versions, escVersion+".mod"), mod, 0o644); err != nil {
		return err
	}
	info, err := json.Marshal(struct {
		Version string
		Time    time.Time
	}{version, t.UTC()})
	if err != nil {
		return err
	}
	if err := os.WriteFile(filepath.Join(versions, escVersion+".info"), info, 0o644); err != nil {
		return err
	}
	list, err := os.ReadFile(filepath.Join(versions, "list"))
	if err != nil && !errors.Is(err, fs.ErrNotExist) {
		return err
	}
	listed := strings.Fields(string(list))
	if !slices.Contains(listed, version) {
		listed = append(listed, version)
	}
	// A proxy can serve root while a test publishes, so the list must never
	// be read half written.
	tmp := filepath.Join(versions, "list.tmp")
	if err := os.WriteFile(tmp, []byte(strings.Join(listed, "\n")+"\n"), 0o644); err != nil {
		return err
	}
	return os.Rename(tmp, filepath.Join(versions, "list"))
}
