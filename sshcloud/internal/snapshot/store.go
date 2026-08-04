// Package snapshot stores Firecracker snapshot packages (state + memory + rootfs + meta).
package snapshot

import (
	"context"
	"encoding/base64"
	"encoding/json"
	"fmt"
	"io"
	"io/fs"
	"os"
	"path/filepath"
	"strings"
	"time"
)

// Meta is persisted beside snapshot artifacts (tap/IP/MAC/rootfs for wake).
// RootfsPath and TapName must be recreated at the same absolute paths before
// snapshot/load — Firecracker embeds them in the snapshot state.
type Meta struct {
	User       string    `json:"user"`
	App        string    `json:"app"`
	GuestIP    string    `json:"guest_ip"`
	TapName    string    `json:"tap_name"`
	GuestMAC   string    `json:"guest_mac"`
	HostIP     string    `json:"host_ip"`
	RootfsPath string    `json:"rootfs_path"`
	Image      string    `json:"image,omitempty"`
	Tier       string    `json:"tier,omitempty"`
	CreatedAt  time.Time `json:"created_at"`
}

// Package is a complete sleep artifact set on local disk before/after blob sync.
type Package struct {
	Dir        string // contains vm.state, vm.mem, rootfs.ext4, meta.json
	Meta       Meta
	StatePath  string
	MemPath    string
	RootfsPath string
	MetaPath   string
}

// NewPackageDir prepares paths under dir.
func NewPackageDir(dir string) Package {
	return Package{
		Dir:        dir,
		StatePath:  filepath.Join(dir, "vm.state"),
		MemPath:    filepath.Join(dir, "vm.mem"),
		RootfsPath: filepath.Join(dir, "rootfs.ext4"),
		MetaPath:   filepath.Join(dir, "meta.json"),
	}
}

// WriteMeta writes meta.json.
func (p Package) WriteMeta(m Meta) error {
	if err := os.MkdirAll(p.Dir, 0o755); err != nil {
		return err
	}
	b, err := json.MarshalIndent(m, "", "  ")
	if err != nil {
		return err
	}
	return os.WriteFile(p.MetaPath, b, 0o644)
}

// ReadMeta loads meta.json.
func (p Package) ReadMeta() (Meta, error) {
	var m Meta
	b, err := os.ReadFile(p.MetaPath)
	if err != nil {
		return m, err
	}
	err = json.Unmarshal(b, &m)
	return m, err
}

// Store persists snapshot packages under an opaque, slash-separated key.
type Store interface {
	// Put uploads all files from a local Package directory.
	Put(ctx context.Context, key string, pkg Package) error
	// Get downloads into destDir and returns a Package pointing there.
	Get(ctx context.Context, key, destDir string) (Package, error)
	// Has reports whether a complete package exists.
	Has(ctx context.Context, key string) (bool, error)
	// Delete removes a stored package.
	Delete(ctx context.Context, key string) error
}

func objectNames() []string {
	return []string{"vm.state", "vm.mem", "rootfs.ext4", "meta.json"}
}

func copyFile(src, dst string) error {
	in, err := os.Open(src)
	if err != nil {
		return err
	}
	defer in.Close()
	if err := os.MkdirAll(filepath.Dir(dst), 0o755); err != nil {
		return err
	}
	out, err := os.Create(dst)
	if err != nil {
		return err
	}
	defer out.Close()
	if _, err := io.Copy(out, in); err != nil {
		return err
	}
	return out.Close()
}

// KeyFor builds an opaque blob key for a user/app. Encoding each component
// prevents caller-controlled identifiers from becoming filesystem or GCS path
// traversal, even if validation is accidentally skipped at an API boundary.
func KeyFor(user, app string) string {
	enc := base64.RawURLEncoding
	return enc.EncodeToString([]byte(user)) + "/" + enc.EncodeToString([]byte(app))
}

func validateKey(key string) error {
	if key == "" || !fs.ValidPath(key) || strings.HasPrefix(key, "/") {
		return fmt.Errorf("invalid snapshot key %q", key)
	}
	return nil
}
