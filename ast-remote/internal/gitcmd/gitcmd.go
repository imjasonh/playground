// Package gitcmd wraps a few git plumbing commands used by the remote helper.
package gitcmd

import (
	"bytes"
	"fmt"
	"os"
	"os/exec"
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

// RevListObjects returns all object OIDs reachable from tips (inclusive),
// optionally excluding objects reachable from notTips.
func (r *Repo) RevListObjects(tips, notTips []string) ([]string, error) {
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
	var oids []string
	seen := map[string]bool{}
	for _, line := range strings.Split(stdout.String(), "\n") {
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}
		oid := strings.Fields(line)[0]
		if len(oid) == 40 && !seen[oid] {
			seen[oid] = true
			oids = append(oids, oid)
		}
	}
	return oids, nil
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
// For trees this is the binary tree format required by hash-object.
func (r *Repo) CatFile(kind, oid string) ([]byte, error) {
	return r.runBytes("cat-file", kind, oid)
}

// HashObject writes raw content as a git object of the given type and returns the OID.
func (r *Repo) HashObject(kind string, data []byte) (string, error) {
	cmd := r.cmd("hash-object", "-w", "-t", kind, "--stdin")
	cmd.Stdin = bytes.NewReader(data)
	var stdout, stderr bytes.Buffer
	cmd.Stdout = &stdout
	cmd.Stderr = &stderr
	if err := cmd.Run(); err != nil {
		return "", fmt.Errorf("git hash-object: %w\n%s", err, stderr.String())
	}
	return strings.TrimSpace(stdout.String()), nil
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
