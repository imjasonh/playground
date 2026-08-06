// Package snapshot stores Firecracker snapshot packages (state + memory + rootfs + meta).
package snapshot

import (
	"context"
	"encoding/base64"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/genid"
	"github.com/imjasonh/playground/sshcloud/internal/names"
)

// Meta is persisted beside snapshot artifacts. LayoutVersion fences the fixed
// paths embedded in Firecracker state; host absolute paths are never trusted.
type Meta struct {
	SchemaVersion    int       `json:"schema_version"`
	LayoutVersion    string    `json:"layout_version"`
	User             string    `json:"user"`
	App              string    `json:"app"`
	Gen              string    `json:"gen,omitempty"`
	GuestIP          string    `json:"guest_ip"`
	TapName          string    `json:"tap_name"`
	GuestMAC         string    `json:"guest_mac"`
	HostIP           string    `json:"host_ip"`
	Image            string    `json:"image,omitempty"`
	Tier             string    `json:"tier,omitempty"`
	PlatformVersion  string    `json:"platform_version,omitempty"`
	SSHHostPublicKey string    `json:"ssh_host_public_key"`
	CreatedAt        time.Time `json:"created_at"`
}

// SchemaVersion 2 rejects the pre-jailer format that persisted absolute host
// rootfs paths. No deployed snapshot data exists to migrate.
const SchemaVersion = 2

const (
	MaxStateBytes    int64 = 128 << 20
	MaxMemoryBytes   int64 = 2 << 30
	MaxRootfsBytes   int64 = 2 << 30
	MaxMetadataBytes int64 = 64 << 10
	MaxPackageBytes        = MaxStateBytes + MaxMemoryBytes + MaxRootfsBytes + MaxMetadataBytes
	MaxRequestBytes        = MaxPackageBytes + (8 << 20)
)

// Ref is the complete tenant snapshot identity. It is passed as structured
// data at every API boundary; callers never supply storage object paths.
type Ref struct {
	User string `json:"user"`
	App  string `json:"app"`
	Gen  string `json:"gen,omitempty"`
}

// Validate rejects ambiguous and non-canonical tenant identities.
func (r Ref) Validate() error {
	if err := names.ValidateIdent(r.User); err != nil {
		return fmt.Errorf("invalid snapshot user: %w", err)
	}
	if err := names.ValidateIdent(r.App); err != nil {
		return fmt.Errorf("invalid snapshot app: %w", err)
	}
	if r.Gen != "" {
		if err := genid.Validate(r.Gen); err != nil {
			return err
		}
	}
	return nil
}

// Key returns the canonical opaque storage key for a structured reference.
func (r Ref) Key() string {
	enc := base64.RawURLEncoding
	return strings.Join([]string{
		"v1",
		"e" + enc.EncodeToString([]byte(r.User)),
		"e" + enc.EncodeToString([]byte(r.App)),
		"e" + enc.EncodeToString([]byte(r.Gen)),
	}, "/")
}

// ParseKey reverses Key and rejects alternate encodings and unsafe identities.
func ParseKey(key string) (Ref, error) {
	parts := strings.Split(key, "/")
	if len(parts) != 4 || parts[0] != "v1" {
		return Ref{}, fmt.Errorf("invalid snapshot key")
	}
	enc := base64.RawURLEncoding
	values := make([]string, 3)
	for i, part := range parts[1:] {
		if !strings.HasPrefix(part, "e") {
			return Ref{}, fmt.Errorf("invalid snapshot key component")
		}
		encoded := strings.TrimPrefix(part, "e")
		value, err := enc.DecodeString(encoded)
		if err != nil || enc.EncodeToString(value) != encoded {
			return Ref{}, fmt.Errorf("invalid snapshot key component")
		}
		values[i] = string(value)
	}
	ref := Ref{User: values[0], App: values[1], Gen: values[2]}
	if err := ref.Validate(); err != nil {
		return Ref{}, err
	}
	if ref.Key() != key {
		return Ref{}, fmt.Errorf("non-canonical snapshot key")
	}
	return ref, nil
}

// RefForAgentApp converts the agent's collision-free app.gen name back to its
// structured placement identity.
func RefForAgentApp(user, agentApp string) Ref {
	app, gen := genid.SplitAgentApp(agentApp)
	return Ref{User: user, App: app, Gen: gen}
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
	if len(b) == 0 || int64(len(b)) > MaxMetadataBytes {
		return fmt.Errorf("snapshot metadata has invalid size %d", len(b))
	}
	return os.WriteFile(p.MetaPath, b, 0o600)
}

// ReadMeta loads meta.json.
func (p Package) ReadMeta() (Meta, error) {
	file, err := os.Open(p.MetaPath)
	if err != nil {
		return Meta{}, err
	}
	defer file.Close()
	info, err := file.Stat()
	if err != nil {
		return Meta{}, err
	}
	if !info.Mode().IsRegular() || info.Size() <= 0 || info.Size() > MaxMetadataBytes {
		return Meta{}, fmt.Errorf("snapshot metadata has invalid type or size %d", info.Size())
	}
	return decodeMeta(file)
}

// Store persists snapshot packages by structured tenant identity.
type Store interface {
	// Put uploads all files from a local Package directory.
	Put(ctx context.Context, ref Ref, pkg Package) error
	// Get downloads into destDir and returns a Package pointing there.
	Get(ctx context.Context, ref Ref, destDir string) (Package, error)
	// Has reports whether a complete package exists.
	Has(ctx context.Context, ref Ref) (bool, error)
	// Meta reads compatibility/identity metadata without downloading memory or disk.
	Meta(ctx context.Context, ref Ref) (Meta, error)
	// Delete removes a stored package.
	Delete(ctx context.Context, ref Ref) error
	// Health verifies that the backing service is available without impersonating
	// a tenant reference.
	Health(ctx context.Context) error
}

// CommitGuard revalidates the authorization decision immediately before a
// mutable current-pointer generation CAS. Long package staging and encryption
// must never extend the lifetime of an expired placement decision.
type CommitGuard func(context.Context) error

// GuardedStore exposes mutation entry points whose current-pointer CAS is
// fenced at the storage boundary. snapshotd requires this interface for remote
// writes and deletes; LocalStore remains usable directly by local KVM mode.
type GuardedStore interface {
	Store
	PutGuarded(context.Context, Ref, Package, CommitGuard) error
	DeleteGuarded(context.Context, Ref, CommitGuard) error
}

// ValidateMeta binds persisted package metadata to its structured identity and
// the server's configured Firecracker layout.
func ValidateMeta(ref Ref, meta Meta, expectedLayout string) error {
	if err := ref.Validate(); err != nil {
		return err
	}
	if meta.User != ref.User || meta.App != ref.App || meta.Gen != ref.Gen {
		return fmt.Errorf("snapshot metadata identity does not match reference")
	}
	if meta.SchemaVersion != SchemaVersion {
		return fmt.Errorf("snapshot schema version %d is unsupported", meta.SchemaVersion)
	}
	if strings.TrimSpace(meta.LayoutVersion) == "" || len(meta.LayoutVersion) > 128 {
		return fmt.Errorf("snapshot layout is invalid")
	}
	if expectedLayout != "" && meta.LayoutVersion != expectedLayout {
		return fmt.Errorf("snapshot layout %q, want %q", meta.LayoutVersion, expectedLayout)
	}
	for field, value := range map[string]string{
		"guest IP": meta.GuestIP, "TAP name": meta.TapName, "guest MAC": meta.GuestMAC,
		"host IP": meta.HostIP, "image": meta.Image, "tier": meta.Tier,
		"platform version": meta.PlatformVersion, "SSH host public key": meta.SSHHostPublicKey,
	} {
		if len(value) > maxMetaFieldBytes(field) || strings.ContainsRune(value, '\x00') {
			return fmt.Errorf("snapshot metadata %s is invalid", field)
		}
	}
	return nil
}

func maxMetaFieldBytes(field string) int {
	switch field {
	case "SSH host public key":
		return 16 << 10
	case "image":
		return 4 << 10
	default:
		return 512
	}
}
