// Package gitcmd wraps git plumbing and writes loose objects natively.
package gitcmd

import (
	"bufio"
	"bytes"
	"compress/zlib"
	"crypto/sha1"
	"encoding/hex"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
)

// Repo is a local git repository (working tree or bare).
type Repo struct {
	Dir    string // working tree (or bare repo) directory
	GitDir string // absolute path to .git (optional; sets GIT_DIR)
}

// New returns a Repo for dir. If gitDir is non-empty it becomes GIT_DIR.
func New(dir, gitDir string) *Repo {
	return &Repo{Dir: dir, GitDir: gitDir}
}

func (r *Repo) objectsDir() (string, error) {
	if r.GitDir != "" {
		return filepath.Join(r.GitDir, "objects"), nil
	}
	// Resolve via git when GitDir unset.
	out, err := r.run("rev-parse", "--git-path", "objects")
	if err != nil {
		return "", err
	}
	p := strings.TrimSpace(out)
	if !filepath.IsAbs(p) {
		p = filepath.Join(r.Dir, p)
	}
	return p, nil
}

func (r *Repo) cmd(args ...string) *exec.Cmd {
	cmd := exec.Command("git", args...)
	cmd.Dir = r.Dir
	env := os.Environ()
	filtered := make([]string, 0, len(env)+1)
	for _, e := range env {
		if strings.HasPrefix(e, "GIT_DIR=") || strings.HasPrefix(e, "GIT_WORK_TREE=") {
			continue
		}
		filtered = append(filtered, e)
	}
	if r.GitDir != "" {
		filtered = append(filtered, "GIT_DIR="+r.GitDir)
	}
	cmd.Env = filtered
	return cmd
}

func (r *Repo) run(args ...string) (string, error) {
	cmd := r.cmd(args...)
	var stdout, stderr bytes.Buffer
	cmd.Stdout = &stdout
	cmd.Stderr = &stderr
	if err := cmd.Run(); err != nil {
		return "", fmt.Errorf("git %s: %w\n%s", strings.Join(args, " "), err, stderr.String())
	}
	return stdout.String(), nil
}

func (r *Repo) runBytes(args ...string) ([]byte, error) {
	cmd := r.cmd(args...)
	var stdout, stderr bytes.Buffer
	cmd.Stdout = &stdout
	cmd.Stderr = &stderr
	if err := cmd.Run(); err != nil {
		return nil, fmt.Errorf("git %s: %w\n%s", strings.Join(args, " "), err, stderr.String())
	}
	return stdout.Bytes(), nil
}

// ObjectInfo is one entry from rev-list --objects (oid + optional path).
type ObjectInfo struct {
	OID  string
	Path string // set for blobs that appear in a tree walk; empty for commits/trees sometimes
}

// RevListObjects returns all object OIDs reachable from tips (inclusive),
// optionally excluding objects reachable from notTips.
func (r *Repo) RevListObjects(tips, notTips []string) ([]string, error) {
	infos, err := r.RevListObjectInfos(tips, notTips)
	if err != nil {
		return nil, err
	}
	oids := make([]string, len(infos))
	for i, info := range infos {
		oids[i] = info.OID
	}
	return oids, nil
}

// RevListObjectInfos is like RevListObjects but keeps path hints from rev-list.
func (r *Repo) RevListObjectInfos(tips, notTips []string) ([]ObjectInfo, error) {
	args := []string{"rev-list", "--objects", "--stdin"}
	var in bytes.Buffer
	for _, t := range tips {
		in.WriteString(t)
		in.WriteByte('\n')
	}
	for _, t := range notTips {
		in.WriteString("^")
		in.WriteString(t)
		in.WriteByte('\n')
	}
	cmd := r.cmd(args...)
	cmd.Stdin = &in
	var stdout, stderr bytes.Buffer
	cmd.Stdout = &stdout
	cmd.Stderr = &stderr
	if err := cmd.Run(); err != nil {
		return nil, fmt.Errorf("git rev-list: %w\n%s", err, stderr.String())
	}
	var out []ObjectInfo
	seen := map[string]bool{}
	for _, line := range strings.Split(stdout.String(), "\n") {
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}
		fields := strings.SplitN(line, " ", 2)
		oid := fields[0]
		if len(oid) != 40 || seen[oid] {
			continue
		}
		seen[oid] = true
		info := ObjectInfo{OID: oid}
		if len(fields) == 2 {
			info.Path = fields[1]
		}
		out = append(out, info)
	}
	return out, nil
}

// CatFileType returns the object type for oid.
func (r *Repo) CatFileType(oid string) (string, error) {
	out, err := r.run("cat-file", "-t", oid)
	if err != nil {
		return "", err
	}
	return strings.TrimSpace(out), nil
}

// CatFile returns the raw object contents for the given type (not pretty-printed).
func (r *Repo) CatFile(kind, oid string) ([]byte, error) {
	return r.runBytes("cat-file", kind, oid)
}

// BatchObject is one result from CatFileBatch.
type BatchObject struct {
	OID  string
	Kind string
	Data []byte
}

// CatFileBatch streams `git cat-file --batch` for the given OIDs.
// Missing objects yield an error.
func (r *Repo) CatFileBatch(oids []string) ([]BatchObject, error) {
	if len(oids) == 0 {
		return nil, nil
	}
	cmd := r.cmd("cat-file", "--batch")
	stdin, err := cmd.StdinPipe()
	if err != nil {
		return nil, err
	}
	stdout, err := cmd.StdoutPipe()
	if err != nil {
		return nil, err
	}
	var stderr bytes.Buffer
	cmd.Stderr = &stderr
	if err := cmd.Start(); err != nil {
		return nil, err
	}

	errCh := make(chan error, 1)
	go func() {
		defer stdin.Close()
		w := bufio.NewWriter(stdin)
		for _, oid := range oids {
			if _, err := w.WriteString(oid + "\n"); err != nil {
				errCh <- err
				return
			}
		}
		errCh <- w.Flush()
	}()

	out := make([]BatchObject, 0, len(oids))
	br := bufio.NewReader(stdout)
	for i := 0; i < len(oids); i++ {
		header, err := br.ReadString('\n')
		if err != nil {
			_ = cmd.Wait()
			return nil, fmt.Errorf("cat-file batch header: %w\n%s", err, stderr.String())
		}
		header = strings.TrimRight(header, "\r\n")
		parts := strings.Fields(header)
		if len(parts) == 2 && parts[1] == "missing" {
			_ = cmd.Wait()
			return nil, fmt.Errorf("object %s missing", parts[0])
		}
		if len(parts) != 3 {
			_ = cmd.Wait()
			return nil, fmt.Errorf("bad cat-file header %q", header)
		}
		oid, kind := parts[0], parts[1]
		var size int
		if _, err := fmt.Sscanf(parts[2], "%d", &size); err != nil {
			_ = cmd.Wait()
			return nil, err
		}
		data := make([]byte, size)
		if _, err := io.ReadFull(br, data); err != nil {
			_ = cmd.Wait()
			return nil, err
		}
		// Trailing newline after payload.
		if _, err := br.ReadByte(); err != nil {
			_ = cmd.Wait()
			return nil, err
		}
		out = append(out, BatchObject{OID: oid, Kind: kind, Data: data})
	}
	if err := <-errCh; err != nil {
		_ = cmd.Process.Kill()
		_ = cmd.Wait()
		return nil, err
	}
	if err := cmd.Wait(); err != nil {
		return nil, fmt.Errorf("cat-file --batch: %w\n%s", err, stderr.String())
	}
	return out, nil
}

// HashObject writes raw content as a git object of the given type and returns the OID.
// Prefer WriteObject for bulk paths — this shells out to git.
func (r *Repo) HashObject(kind string, data []byte) (string, error) {
	return r.WriteObject(kind, data)
}

// WriteObject writes a loose object natively (zlib + SHA-1) and returns the OID.
// If expectedOID is non-empty, the computed hash must match it.
func (r *Repo) WriteObject(kind string, data []byte) (string, error) {
	return r.WriteObjectExpected(kind, data, "")
}

// WriteObjectExpected is WriteObject with an optional expected OID check.
func (r *Repo) WriteObjectExpected(kind string, data []byte, expectedOID string) (string, error) {
	header := fmt.Sprintf("%s %d\x00", kind, len(data))
	h := sha1.New()
	_, _ = h.Write([]byte(header))
	_, _ = h.Write(data)
	oid := hex.EncodeToString(h.Sum(nil))
	if expectedOID != "" && oid != expectedOID {
		return "", fmt.Errorf("oid mismatch: got %s want %s", oid, expectedOID)
	}

	objDir, err := r.objectsDir()
	if err != nil {
		return "", err
	}
	dir := filepath.Join(objDir, oid[:2])
	path := filepath.Join(dir, oid[2:])
	if _, err := os.Stat(path); err == nil {
		return oid, nil // already present
	}
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return "", err
	}

	var buf bytes.Buffer
	zw, zerr := zlib.NewWriterLevel(&buf, zlib.BestSpeed)
	if zerr != nil {
		return "", zerr
	}
	if _, err := zw.Write([]byte(header)); err != nil {
		return "", err
	}
	if _, err := zw.Write(data); err != nil {
		return "", err
	}
	if err := zw.Close(); err != nil {
		return "", err
	}

	tmp := path + ".tmp"
	if err := os.WriteFile(tmp, buf.Bytes(), 0o444); err != nil {
		return "", err
	}
	if err := os.Rename(tmp, path); err != nil {
		_ = os.Remove(tmp)
		// Race: another writer won.
		if _, statErr := os.Stat(path); statErr == nil {
			return oid, nil
		}
		return "", err
	}
	return oid, nil
}

// UpdateRef sets ref to oid.
func (r *Repo) UpdateRef(ref, oid string) error {
	_, err := r.run("update-ref", ref, oid)
	return err
}

// SymbolicRef reads a symbolic ref (e.g. HEAD).
func (r *Repo) SymbolicRef(name string) (string, error) {
	out, err := r.run("symbolic-ref", "-q", name)
	if err != nil {
		return "", err
	}
	return strings.TrimSpace(out), nil
}

// ShowRef lists local refs as name→oid.
func (r *Repo) ShowRef() (map[string]string, error) {
	out, err := r.run("show-ref")
	if err != nil {
		// empty repo
		if strings.Contains(err.Error(), "exit status 1") {
			return map[string]string{}, nil
		}
		return nil, err
	}
	m := map[string]string{}
	for _, line := range strings.Split(out, "\n") {
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}
		parts := strings.Fields(line)
		if len(parts) >= 2 {
			m[parts[1]] = parts[0]
		}
	}
	return m, nil
}

// LsTreePaths returns path→blobOID for all blobs under treeish (recursive).
func (r *Repo) LsTreePaths(treeish string) (map[string]string, error) {
	out, err := r.run("ls-tree", "-r", treeish)
	if err != nil {
		return nil, err
	}
	m := map[string]string{}
	for _, line := range strings.Split(out, "\n") {
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}
		// mode type oid\tpath
		parts := strings.SplitN(line, "\t", 2)
		if len(parts) != 2 {
			continue
		}
		fields := strings.Fields(parts[0])
		if len(fields) < 3 {
			continue
		}
		if fields[1] == "blob" {
			m[parts[1]] = fields[2]
		}
	}
	return m, nil
}

// RevParse resolves a revision to an OID.
func (r *Repo) RevParse(rev string) (string, error) {
	out, err := r.run("rev-parse", rev)
	if err != nil {
		return "", err
	}
	return strings.TrimSpace(out), nil
}

// PackObjects builds a native packfile for the given tips via git pack-objects.
func (r *Repo) PackObjects(tips []string) ([]byte, error) {
	var revListIn bytes.Buffer
	for _, t := range tips {
		revListIn.WriteString(t)
		revListIn.WriteByte('\n')
	}
	revList := r.cmd("rev-list", "--objects", "--stdin")
	revList.Stdin = &revListIn
	pack := r.cmd("pack-objects", "--stdout", "--all-progress-implied")
	var packOut, errBuf bytes.Buffer
	pack.Stdout = &packOut
	pack.Stderr = &errBuf

	pr, pw := io.Pipe()
	revList.Stdout = pw
	pack.Stdin = pr

	if err := revList.Start(); err != nil {
		return nil, err
	}
	if err := pack.Start(); err != nil {
		_ = revList.Process.Kill()
		return nil, err
	}
	revErr := make(chan error, 1)
	go func() {
		revErr <- revList.Wait()
		_ = pw.Close()
	}()
	packErr := pack.Wait()
	if err := <-revErr; err != nil {
		return nil, fmt.Errorf("rev-list: %w", err)
	}
	if packErr != nil {
		return nil, fmt.Errorf("pack-objects: %w\n%s", packErr, errBuf.String())
	}
	return packOut.Bytes(), nil
}
