package layout

import (
	"archive/tar"
	"compress/gzip"
	"crypto/md5"
	"encoding/base32"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strings"
	"unicode"

	"github.com/imjasonh/playground/node-image/internal/lock"
	"github.com/imjasonh/playground/node-image/internal/resolve"
)

// Result is a materialized node_modules tree under Root.
type Result struct {
	Root string
}

// Materialize extracts packages into root/node_modules using a pnpm-like virtual store.
// tarballs maps PackageID → local .tgz path.
// Edges from the lock are used to create store-internal dependency symlinks.
// Only importer direct dependencies are linked at the top level (plus root .bin).
// direct binds top-level link names (including aliases) to resolved dep paths.
func Materialize(root string, l *lock.Lock, refs []resolve.PackageRef, tarballs map[string]string, direct []resolve.DirectDep) (*Result, error) {
	nm := filepath.Join(root, "node_modules")
	store := filepath.Join(nm, ".pnpm")
	if err := os.MkdirAll(store, 0o755); err != nil {
		return nil, err
	}

	byDepPath := make(map[string]resolve.PackageRef, len(refs))
	for _, ref := range refs {
		byDepPath[ref.DepPath] = ref
	}

	type installed struct {
		ref     resolve.PackageRef
		pkgDir  string
		pkgJSON packageJSON
	}
	inst := make([]installed, 0, len(refs))

	for _, ref := range refs {
		tgz, ok := tarballs[ref.PackageID]
		if !ok {
			return nil, fmt.Errorf("missing tarball for %s", ref.PackageID)
		}
		depDir := filepath.Join(store, VirtualStoreDir(ref.DepPath), "node_modules")
		pkgDir := filepath.Join(depDir, filepath.FromSlash(ref.Name))
		if err := os.MkdirAll(filepath.Dir(pkgDir), 0o755); err != nil {
			return nil, err
		}
		if err := extractNPMTarball(tgz, pkgDir); err != nil {
			return nil, fmt.Errorf("extract %s: %w", ref.PackageID, err)
		}
		pj, err := readPackageJSON(pkgDir)
		if err != nil {
			return nil, fmt.Errorf("%s package.json: %w", ref.PackageID, err)
		}
		if err := CheckScriptsInDir(ref, pkgDir, pj); err != nil {
			return nil, err
		}
		inst = append(inst, installed{ref: ref, pkgDir: pkgDir, pkgJSON: pj})
	}

	for _, in := range inst {
		snap := l.Snapshots[in.ref.DepPath]
		if snap == nil {
			snap = l.Snapshots[in.ref.PackageID]
		}
		if snap != nil {
			var deps []namedDep
			add := func(depName, ver string) {
				depPath := resolve.DepPathFrom(depName, ver)
				var ref resolve.PackageRef
				var ok bool
				if ref, ok = byDepPath[depPath]; !ok {
					if ref, ok = byDepPath[ver]; !ok {
						for _, r := range refs {
							if r.PackageID == ver || r.DepPath == ver || r.PackageID == depPath || r.DepPath == depPath {
								ref = r
								ok = true
								break
							}
						}
					}
				}
				if !ok {
					return // filtered optional / missing
				}
				deps = append(deps, namedDep{linkName: depName, ref: ref})
			}
			for depName, ver := range snap.Dependencies {
				add(depName, ver)
			}
			for depName, ver := range snap.OptionalDependencies {
				add(depName, ver)
			}
			if err := linkStoreDeps(root, in.ref, deps); err != nil {
				return nil, err
			}
		}
		// Bins inside the virtual store node_modules (pnpm-compatible).
		if err := writeBins(filepath.Dir(in.pkgDir), in.pkgDir, in.pkgJSON); err != nil {
			return nil, err
		}
	}

	if err := LinkTopLevel(root, refs, direct); err != nil {
		return nil, err
	}
	// Root node_modules/.bin for direct deps that expose bins.
	if err := linkRootBins(root, byDepPath, direct); err != nil {
		return nil, err
	}
	return &Result{Root: root}, nil
}

// DefaultVirtualStoreDirMaxLength is pnpm's default virtualStoreDirMaxLength on
// Linux/macOS (see pnpm's virtual-store-dir-max-length). Paths longer than this
// (or with uppercase letters) are truncated and given a base32(md5) suffix —
// without that, peer-heavy Nest/ESLint graphs exceed Linux NAME_MAX (255).
const DefaultVirtualStoreDirMaxLength = 120

// base32HashLen is the length of createBase32Hash output (md5 → base32, no pad).
const base32HashLen = 26

// VirtualStoreDir encodes a lock depPath the way pnpm names directories under
// node_modules/.pnpm (pnpm 9.x / lockfile v9):
//
//	depPathToFilename: '/' and other illegal chars → '+';
//	strip a trailing ')'; then ')(' / '(' / ')' → '_';
//	if len > max or mixed case → truncate + '_' + base32(md5).
//
// e.g. "@scope/pkg@1.0.0(peer@2)" → "@scope+pkg@1.0.0_peer@2"
func VirtualStoreDir(depPath string) string {
	return VirtualStoreDirMax(depPath, DefaultVirtualStoreDirMaxLength)
}

// VirtualStoreDirMax is VirtualStoreDir with an explicit max length (pnpm's
// virtualStoreDirMaxLength). maxLength <= 0 uses the default.
func VirtualStoreDirMax(depPath string, maxLength int) string {
	if maxLength <= 0 {
		maxLength = DefaultVirtualStoreDirMaxLength
	}
	filename := depPathToFilenameUnescaped(depPath)
	// pnpm 9: replace / \ : * ? " < > |
	filename = strings.Map(func(r rune) rune {
		switch r {
		case '/', '\\', ':', '*', '?', '"', '<', '>', '|':
			return '+'
		default:
			return r
		}
	}, filename)
	if strings.Contains(filename, "(") {
		filename = strings.TrimSuffix(filename, ")")
		// ')(' | '(' | ')' → '_'  (order matters: collapse peer-group seams first)
		var b strings.Builder
		b.Grow(len(filename))
		for i := 0; i < len(filename); i++ {
			c := filename[i]
			if c == ')' && i+1 < len(filename) && filename[i+1] == '(' {
				b.WriteByte('_')
				i++
				continue
			}
			if c == '(' || c == ')' {
				b.WriteByte('_')
				continue
			}
			b.WriteByte(c)
		}
		filename = b.String()
	}
	needsHash := len(filename) > maxLength || (filename != strings.ToLower(filename) && !strings.HasPrefix(filename, "file+"))
	if !needsHash {
		return filename
	}
	// pnpm 9.12: substring(0, maxLength - 27) + '_' + createBase32Hash
	keep := maxLength - base32HashLen - 1
	if keep < 0 {
		keep = 0
	}
	if keep > len(filename) {
		keep = len(filename)
	}
	return filename[:keep] + "_" + createBase32Hash(filename)
}

func depPathToFilenameUnescaped(depPath string) string {
	if strings.HasPrefix(depPath, "file:") {
		return strings.Replace(depPath, ":", "+", 1)
	}
	if strings.HasPrefix(depPath, "/") {
		depPath = depPath[1:]
	}
	// pnpm rewrites name@version around the '@' after index 0; for registry
	// packages this is a no-op (same string). Kept for file:/ absolute forms.
	index := -1
	if len(depPath) > 1 {
		index = strings.IndexByte(depPath[1:], '@')
		if index >= 0 {
			index++ // restore absolute index
		}
	}
	if index == -1 {
		return depPath
	}
	return depPath[:index] + "@" + depPath[index+1:]
}

func createBase32Hash(s string) string {
	sum := md5.Sum([]byte(s))
	enc := base32.StdEncoding.WithPadding(base32.NoPadding).EncodeToString(sum[:])
	return strings.Map(func(r rune) rune {
		return unicode.ToLower(r)
	}, enc)
}

// LinkTopLevel creates node_modules/<linkName> → .pnpm/.../node_modules/<pkgName>
// for importer direct dependencies. linkName may be an alias (npm:…).
func LinkTopLevel(root string, refs []resolve.PackageRef, direct []resolve.DirectDep) error {
	nm := filepath.Join(root, "node_modules")
	byDepPath := make(map[string]resolve.PackageRef, len(refs))
	for _, ref := range refs {
		byDepPath[ref.DepPath] = ref
	}
	links := direct
	if len(links) == 0 {
		// Back-compat: if caller didn't pass directs, link every package by its real name.
		for _, ref := range refs {
			links = append(links, resolve.DirectDep{LinkName: ref.Name, DepPath: ref.DepPath})
		}
	}
	for _, d := range links {
		ref, ok := byDepPath[d.DepPath]
		if !ok {
			// Try package-id form / alias target already encoded as dep path.
			for _, r := range refs {
				if r.PackageID == d.DepPath || r.DepPath == d.DepPath {
					ref = r
					ok = true
					break
				}
			}
		}
		if !ok {
			return fmt.Errorf("direct dependency %q → %q not found in resolved closure", d.LinkName, d.DepPath)
		}
		targetAbs := filepath.Join(nm, ".pnpm", VirtualStoreDir(ref.DepPath), "node_modules", filepath.FromSlash(ref.Name))
		link := filepath.Join(nm, filepath.FromSlash(d.LinkName))
		if err := os.MkdirAll(filepath.Dir(link), 0o755); err != nil {
			return err
		}
		rel, err := filepath.Rel(filepath.Dir(link), targetAbs)
		if err != nil {
			return err
		}
		_ = os.Remove(link)
		if err := os.Symlink(rel, link); err != nil {
			return fmt.Errorf("symlink %s: %w", link, err)
		}
	}
	return nil
}

func linkRootBins(root string, byDepPath map[string]resolve.PackageRef, direct []resolve.DirectDep) error {
	nm := filepath.Join(root, "node_modules")
	links := direct
	if len(links) == 0 {
		for _, ref := range byDepPath {
			links = append(links, resolve.DirectDep{LinkName: ref.Name, DepPath: ref.DepPath})
		}
	}
	seen := map[string]struct{}{}
	for _, d := range links {
		ref, ok := byDepPath[d.DepPath]
		if !ok {
			continue
		}
		if _, dup := seen[ref.DepPath]; dup {
			continue
		}
		seen[ref.DepPath] = struct{}{}
		pkgDir := filepath.Join(root, "node_modules", ".pnpm", VirtualStoreDir(ref.DepPath), "node_modules", filepath.FromSlash(ref.Name))
		pj, err := readPackageJSON(pkgDir)
		if err != nil {
			continue
		}
		if err := writeBins(nm, pkgDir, pj); err != nil {
			return err
		}
	}
	return nil
}

type namedDep struct {
	linkName string
	ref      resolve.PackageRef
}

func linkStoreDeps(root string, parent resolve.PackageRef, deps []namedDep) error {
	parentNM := filepath.Join(root, "node_modules", ".pnpm", VirtualStoreDir(parent.DepPath), "node_modules")
	for _, dep := range deps {
		depPkg := filepath.Join(root, "node_modules", ".pnpm", VirtualStoreDir(dep.ref.DepPath), "node_modules", filepath.FromSlash(dep.ref.Name))
		link := filepath.Join(parentNM, filepath.FromSlash(dep.linkName))
		if _, err := os.Lstat(link); err == nil {
			continue
		}
		if err := os.MkdirAll(filepath.Dir(link), 0o755); err != nil {
			return err
		}
		rel, err := filepath.Rel(filepath.Dir(link), depPkg)
		if err != nil {
			return err
		}
		if err := os.Symlink(rel, link); err != nil {
			return err
		}
	}
	return nil
}

type packageJSON struct {
	Name                 string                     `json:"name"`
	Version              string                     `json:"version"`
	Bin                  json.RawMessage            `json:"bin"`
	Directories          *directoriesJSON           `json:"directories"`
	Scripts              map[string]json.RawMessage `json:"scripts"`
	OptionalDependencies map[string]string          `json:"optionalDependencies"`
}

type directoriesJSON struct {
	Bin string `json:"bin"`
}

func readPackageJSON(dir string) (packageJSON, error) {
	var pj packageJSON
	b, err := os.ReadFile(filepath.Join(dir, "package.json"))
	if err != nil {
		return pj, err
	}
	if err := json.Unmarshal(b, &pj); err != nil {
		return pj, err
	}
	return pj, nil
}

// scriptString returns a lifecycle script body when it is a JSON string.
// Some packages (e.g. alce) stash non-string values under scripts.* — ignore those.
func (pj packageJSON) scriptString(name string) string {
	if pj.Scripts == nil {
		return ""
	}
	raw, ok := pj.Scripts[name]
	if !ok || len(raw) == 0 {
		return ""
	}
	var s string
	if err := json.Unmarshal(raw, &s); err != nil {
		return ""
	}
	return s
}

// CheckScriptsInDir fails when a non-optional package appears to need a native
// compile (node-gyp / binding.gyp) and has no prebuilds or platform optionals.
// Telemetry / no-op postinstall scripts (e.g. @scarf/scarf) are allowed — we
// never run them, and the package still works.
func CheckScriptsInDir(ref resolve.PackageRef, pkgDir string, pj packageJSON) error {
	if ref.Optional {
		return nil
	}
	hasPrebuilds := false
	if st, err := os.Stat(filepath.Join(pkgDir, "prebuilds")); err == nil && st.IsDir() {
		hasPrebuilds = true
	}
	hasPlatformOptionals := false
	if pj.OptionalDependencies != nil {
		for name := range pj.OptionalDependencies {
			if strings.Contains(name, "/") && (strings.Contains(name, "linux-") || strings.Contains(name, "darwin-") || strings.Contains(name, "win32-")) {
				hasPlatformOptionals = true
				break
			}
		}
	}
	if hasPrebuilds || hasPlatformOptionals {
		return nil
	}

	needsNative := false
	if _, err := os.Stat(filepath.Join(pkgDir, "binding.gyp")); err == nil {
		needsNative = true
	}
	for _, s := range []string{"preinstall", "install", "postinstall"} {
		body := pj.scriptString(s)
		if body == "" {
			continue
		}
		lower := strings.ToLower(body)
		if strings.Contains(lower, "node-gyp") ||
			strings.Contains(lower, "node-pre-gyp") ||
			strings.Contains(lower, "prebuild-install") ||
			strings.Contains(lower, "nan ") ||
			strings.Contains(lower, "cmake-js") {
			needsNative = true
			break
		}
	}
	if !needsNative {
		return nil
	}
	return fmt.Errorf("package %s appears to require a native build (node-gyp/binding.gyp) and node-image never runs dependency install scripts\nHint: prefer packages that ship prebuilds/ or platform-specific optionalDependencies (e.g. @esbuild/linux-x64). Remove or replace %s if it must compile from source", ref.PackageID, ref.PackageID)
}

func writeBins(nodeModulesDir, pkgDir string, pj packageJSON) error {
	bins, err := parseBin(pj)
	if err != nil || len(bins) == 0 {
		return err
	}
	binDir := filepath.Join(nodeModulesDir, ".bin")
	if err := os.MkdirAll(binDir, 0o755); err != nil {
		return err
	}
	for name, rel := range bins {
		target := filepath.Join(pkgDir, filepath.FromSlash(rel))
		link := filepath.Join(binDir, name)
		relTarget, err := filepath.Rel(binDir, target)
		if err != nil {
			return err
		}
		_ = os.Remove(link)
		if err := os.Symlink(relTarget, link); err != nil {
			return err
		}
	}
	return nil
}

func parseBin(pj packageJSON) (map[string]string, error) {
	out := map[string]string{}
	if len(pj.Bin) != 0 && string(pj.Bin) != "null" {
		var asString string
		if err := json.Unmarshal(pj.Bin, &asString); err == nil {
			name := pj.Name
			if i := strings.LastIndex(name, "/"); i >= 0 {
				name = name[i+1:]
			}
			out[name] = asString
		} else {
			var asMap map[string]string
			if err := json.Unmarshal(pj.Bin, &asMap); err != nil {
				return nil, err
			}
			for k, v := range asMap {
				out[k] = v
			}
		}
	}
	if pj.Directories != nil && pj.Directories.Bin != "" {
		// directories.bin is a directory of executables; we only record the dir
		// marker by linking each file when present on disk — caller may not
		// have extracted yet, so skip if missing.
		binDir := filepath.Join(filepath.Dir(pj.Name), pj.Directories.Bin) // unused path helper
		_ = binDir
	}
	return out, nil
}

func extractNPMTarball(tgzPath, destDir string) error {
	destAbs, err := filepath.Abs(destDir)
	if err != nil {
		return err
	}
	if err := os.MkdirAll(destAbs, 0o755); err != nil {
		return err
	}
	prefix, err := npmTarballRootPrefix(tgzPath)
	if err != nil {
		return err
	}
	f, err := os.Open(tgzPath)
	if err != nil {
		return err
	}
	defer f.Close()
	gr, err := gzip.NewReader(f)
	if err != nil {
		return err
	}
	defer gr.Close()
	tr := tar.NewReader(gr)
	for {
		hdr, err := tr.Next()
		if err == io.EOF {
			break
		}
		if err != nil {
			return err
		}
		name := strings.TrimPrefix(hdr.Name, "./")
		if prefix != "" {
			if name == strings.TrimSuffix(prefix, "/") {
				continue // root dir entry
			}
			if !strings.HasPrefix(name, prefix) {
				continue
			}
			name = strings.TrimPrefix(name, prefix)
		}
		if name == "" {
			continue
		}
		clean := filepath.Clean(filepath.FromSlash(name))
		if clean == "." || clean == ".." || strings.HasPrefix(clean, ".."+string(os.PathSeparator)) || filepath.IsAbs(clean) {
			return fmt.Errorf("refusing unsafe path in tarball: %s", hdr.Name)
		}
		out := filepath.Join(destAbs, clean)
		// Ensure the joined path stays under destAbs even if Clean tricks slip through.
		if !isWithinDir(destAbs, out) {
			return fmt.Errorf("refusing path escape in tarball: %s", hdr.Name)
		}
		switch hdr.Typeflag {
		case tar.TypeDir:
			if err := os.MkdirAll(out, 0o755); err != nil {
				return err
			}
		case tar.TypeReg, tar.TypeRegA:
			if err := os.MkdirAll(filepath.Dir(out), 0o755); err != nil {
				return err
			}
			// Do not follow a symlink when creating the file (symlink escape).
			mode := hdr.FileInfo().Mode().Perm()
			w, err := os.OpenFile(out, os.O_CREATE|os.O_WRONLY|os.O_TRUNC|os.O_EXCL, mode)
			if err != nil {
				// If something already exists, refuse to overwrite through a symlink.
				if st, lerr := os.Lstat(out); lerr == nil && st.Mode()&os.ModeSymlink != 0 {
					return fmt.Errorf("refusing to write through symlink in tarball: %s", hdr.Name)
				}
				_ = os.Remove(out)
				w, err = os.OpenFile(out, os.O_CREATE|os.O_WRONLY|os.O_TRUNC|os.O_EXCL, mode)
				if err != nil {
					return err
				}
			}
			if _, err := io.Copy(w, tr); err != nil {
				w.Close()
				return err
			}
			if err := w.Close(); err != nil {
				return err
			}
		case tar.TypeSymlink:
			target := hdr.Linkname
			if filepath.IsAbs(target) || strings.HasPrefix(filepath.Clean(target), "..") {
				return fmt.Errorf("refusing unsafe symlink target in tarball: %s -> %s", hdr.Name, target)
			}
			// Resolve relative to the link's directory and require it stay in destAbs.
			linkDir := filepath.Dir(out)
			resolved := filepath.Clean(filepath.Join(linkDir, filepath.FromSlash(target)))
			if !isWithinDir(destAbs, resolved) {
				return fmt.Errorf("refusing symlink escape in tarball: %s -> %s", hdr.Name, target)
			}
			if err := os.MkdirAll(linkDir, 0o755); err != nil {
				return err
			}
			_ = os.Remove(out)
			if err := os.Symlink(target, out); err != nil {
				return err
			}
		case tar.TypeLink:
			return fmt.Errorf("refusing hardlink in tarball: %s", hdr.Name)
		}
	}
	return nil
}

// npmTarballRootPrefix returns the single top-level directory prefix to strip
// (e.g. "package/" or "ejs-v3.1.10/"). npm pack uses "package/"; some older or
// republished tarballs use "{name}-v{version}/" or "{name}/". If entries do not
// share one root, returns "" (extract as-is).
func npmTarballRootPrefix(tgzPath string) (string, error) {
	f, err := os.Open(tgzPath)
	if err != nil {
		return "", err
	}
	defer f.Close()
	gr, err := gzip.NewReader(f)
	if err != nil {
		return "", err
	}
	defer gr.Close()
	tr := tar.NewReader(gr)
	var root string
	for {
		hdr, err := tr.Next()
		if err == io.EOF {
			break
		}
		if err != nil {
			return "", err
		}
		name := strings.TrimPrefix(hdr.Name, "./")
		if name == "" || name == "." {
			continue
		}
		parts := strings.SplitN(name, "/", 2)
		top := parts[0]
		if root == "" {
			root = top
			continue
		}
		if top != root {
			return "", nil // mixed roots — do not strip
		}
	}
	if root == "" {
		return "", nil
	}
	return root + "/", nil
}

func isWithinDir(root, path string) bool {
	root = filepath.Clean(root)
	path = filepath.Clean(path)
	if path == root {
		return true
	}
	sep := string(os.PathSeparator)
	return strings.HasPrefix(path, root+sep)
}

// ExtractNPMTarballForTest exposes extractNPMTarball for security tests.
func ExtractNPMTarballForTest(tgzPath, destDir string) error {
	return extractNPMTarball(tgzPath, destDir)
}

// ReadPackageJSONForTest exposes readPackageJSON for policy tests.
func ReadPackageJSONForTest(dir string) (packageJSON, error) {
	return readPackageJSON(dir)
}

