// Package snapshot stores Firecracker snapshot packages (state + memory + rootfs + meta).
package snapshot

import (
	"context"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"path/filepath"
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

// Store persists snapshot packages under a key (e.g. "alice/fortune").
type Store interface {
	// Put uploads all files from a local Package directory.
	Put(ctx context.Context, key string, pkg Package) error
	// Get downloads into destDir and returns a Package pointing there.
	Get(ctx context.Context, key, destDir string) (Package, error)
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

// KeyFor builds the blob key prefix for a user/app.
func KeyFor(user, app string) string {
	return fmt.Sprintf("%s/%s", user, app)
}
