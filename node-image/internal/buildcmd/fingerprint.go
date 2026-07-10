package buildcmd

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"sort"
	"time"

	"github.com/imjasonh/playground/node-image/internal/config"
	"github.com/imjasonh/playground/node-image/internal/resolve"
)

// buildRecord is the on-disk short-circuit cache for a fully identical rebuild.
type buildRecord struct {
	Fingerprint      string    `json:"fingerprint"`
	Ref              string    `json:"ref"`
	Platforms        []string  `json:"platforms"`
	CreatedAt        time.Time `json:"createdAt"`
	LayersSummary    string    `json:"layersSummary,omitempty"`
	PlatformsSummary string    `json:"platformsSummary,omitempty"`
}

// buildFingerprint inputs that determine image content for a no-op check.
type buildFingerprintInput struct {
	LockDigest   string
	Importer     string
	Platforms    []string
	Base         string
	Workdir      string
	User         string
	Entrypoint   []string
	Cmd          []string
	Env          []string
	Include      []string
	Exclude      []string
	MaxLayers    int
	Unbucketed   []string
	AllowScripts []string
	EmptyBase    bool
	// OutputMode is "nopush", "push", or "local" so refs aren't mixed.
	OutputMode string
	Repo       string
	// ClosureKeys is sorted "packageID=integrityOrLocalKey" lines.
	ClosureKeys []string
	// AppOutputs is sorted "rel=size:mtime" lines for packed app files.
	AppOutputs []string
}

func (in buildFingerprintInput) digest() string {
	h := sha256.New()
	enc := json.NewEncoder(h)
	_ = enc.Encode(in)
	return hex.EncodeToString(h.Sum(nil))
}

func buildCacheDir(cacheRoot string) (string, error) {
	dir := filepath.Join(cacheRoot, "builds")
	if err := os.MkdirAll(dir, 0o700); err != nil {
		return "", err
	}
	return dir, nil
}

func lookupBuildRecord(cacheRoot, fingerprint string) (*buildRecord, bool) {
	dir, err := buildCacheDir(cacheRoot)
	if err != nil {
		return nil, false
	}
	b, err := os.ReadFile(filepath.Join(dir, fingerprint+".json"))
	if err != nil {
		return nil, false
	}
	var rec buildRecord
	if json.Unmarshal(b, &rec) != nil || rec.Ref == "" || rec.Fingerprint != fingerprint {
		return nil, false
	}
	return &rec, true
}

func storeBuildRecord(cacheRoot string, rec buildRecord) error {
	dir, err := buildCacheDir(cacheRoot)
	if err != nil {
		return err
	}
	b, err := json.MarshalIndent(rec, "", "  ")
	if err != nil {
		return err
	}
	tmp := filepath.Join(dir, rec.Fingerprint+".tmp")
	final := filepath.Join(dir, rec.Fingerprint+".json")
	if err := os.WriteFile(tmp, append(b, '\n'), 0o600); err != nil {
		return err
	}
	return os.Rename(tmp, final)
}

func lockFileDigest(lockPath string) (string, error) {
	b, err := os.ReadFile(lockPath)
	if err != nil {
		return "", err
	}
	sum := sha256.Sum256(b)
	return hex.EncodeToString(sum[:]), nil
}

func closureKeyLines(refs []resolve.PackageRef, integrityKeys map[string]string) []string {
	lines := make([]string, 0, len(refs))
	for _, ref := range refs {
		key := integrityKeys[ref.PackageID]
		if key == "" {
			key = ref.Integrity
		}
		lines = append(lines, ref.PackageID+"="+key)
	}
	sort.Strings(lines)
	return lines
}

func appOutputLines(outputs map[string]string) ([]string, error) {
	rels := make([]string, 0, len(outputs))
	for rel := range outputs {
		rels = append(rels, rel)
	}
	sort.Strings(rels)
	lines := make([]string, 0, len(rels))
	for _, rel := range rels {
		st, err := os.Stat(outputs[rel])
		if err != nil {
			return nil, err
		}
		lines = append(lines, fmt.Sprintf("%s=%d:%d", rel, st.Size(), st.ModTime().UnixNano()))
	}
	return lines, nil
}

func fingerprintFromConfig(cfg *config.Config, lockDigest, importer string, platforms []string, emptyBase bool, closureKeys, appOuts []string) string {
	mode := "push"
	if cfg.Local {
		mode = "local"
	} else if cfg.NoPush {
		mode = "nopush"
	}
	in := buildFingerprintInput{
		LockDigest:   lockDigest,
		Importer:     importer,
		Platforms:    append([]string(nil), platforms...),
		Base:         cfg.Base,
		Workdir:      cfg.Workdir,
		User:         cfg.User,
		Entrypoint:   append([]string(nil), cfg.Entrypoint...),
		Cmd:          cfg.Cmd(),
		Env:          cfg.EnvList(),
		Include:      append([]string(nil), cfg.Include...),
		Exclude:      append([]string(nil), cfg.Exclude...),
		MaxLayers:    cfg.MaxLayers,
		Unbucketed:   append([]string(nil), cfg.Unbucketed...),
		AllowScripts: append([]string(nil), cfg.AllowScripts...),
		EmptyBase:    emptyBase,
		OutputMode:   mode,
		Repo:         cfg.Repo,
		ClosureKeys:  closureKeys,
		AppOutputs:   appOuts,
	}
	sort.Strings(in.Platforms)
	return in.digest()
}

func cacheRootFor(cfg *config.Config) string {
	if cfg.CacheDir != "" {
		return cfg.CacheDir
	}
	home, err := os.UserHomeDir()
	if err != nil {
		return ""
	}
	return filepath.Join(home, ".cache", "node-image")
}

func sameStringSet(a, b []string) bool {
	if len(a) != len(b) {
		return false
	}
	ma := map[string]int{}
	for _, s := range a {
		ma[s]++
	}
	for _, s := range b {
		ma[s]--
		if ma[s] < 0 {
			return false
		}
	}
	return true
}

func writeCachedDigestSummary(dir string, rec *buildRecord) error {
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return err
	}
	if err := os.WriteFile(filepath.Join(dir, "digest"), []byte(rec.Ref), 0o644); err != nil {
		return err
	}
	if rec.LayersSummary != "" {
		if err := os.WriteFile(filepath.Join(dir, "layers"), []byte(rec.LayersSummary), 0o644); err != nil {
			return err
		}
	}
	if rec.PlatformsSummary != "" {
		if err := os.WriteFile(filepath.Join(dir, "platforms"), []byte(rec.PlatformsSummary), 0o644); err != nil {
			return err
		}
	}
	return nil
}
