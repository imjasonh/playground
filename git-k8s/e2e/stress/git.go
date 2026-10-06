package main

import (
	"bytes"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"sync"
	"time"
)

// gitRepo is a working copy of one repository on the git server, which
// plays the developers who push to it. Its methods hold mu, so one
// operation runs at a time.
type gitRepo struct {
	mu  sync.Mutex
	dir string
	url string
}

// author is who makes a commit.
type author struct{ name, email string }

func (g *gitRepo) git(env []string, args ...string) (string, error) {
	cmd := exec.Command("git", append([]string{"-C", g.dir, "-c", "advice.detachedHead=false", "-c", "core.hooksPath=/dev/null"}, args...)...)
	// The machine's git config can name a proxy that can't reach the git
	// server, so leave it out.
	cmd.Env = append(os.Environ(), "GIT_CONFIG_GLOBAL=/dev/null", "GIT_CONFIG_NOSYSTEM=1", "GIT_TERMINAL_PROMPT=0",
		"NO_PROXY=127.0.0.1,localhost", "no_proxy=127.0.0.1,localhost",
		"GIT_AUTHOR_NAME=stress", "GIT_AUTHOR_EMAIL=stress@example.com",
		"GIT_COMMITTER_NAME=stress", "GIT_COMMITTER_EMAIL=stress@example.com")
	cmd.Env = append(cmd.Env, env...)
	var out bytes.Buffer
	cmd.Stdout, cmd.Stderr = &out, &out
	if err := cmd.Run(); err != nil {
		return out.String(), fmt.Errorf("git %s: %w: %s", strings.Join(args, " "), err, strings.TrimSpace(out.String()))
	}
	return strings.TrimSpace(out.String()), nil
}

func authorEnv(a author) []string {
	return []string{"GIT_AUTHOR_NAME=" + a.name, "GIT_AUTHOR_EMAIL=" + a.email, "GIT_COMMITTER_NAME=" + a.name, "GIT_COMMITTER_EMAIL=" + a.email}
}

// initRepo creates the working copy with files on main and pushes main.
func initRepo(dir, url string, files map[string]string) (*gitRepo, error) {
	if err := os.RemoveAll(dir); err != nil {
		return nil, err
	}
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return nil, err
	}
	g := &gitRepo{dir: dir, url: url}
	if _, err := g.git(nil, "init", "-q", "-b", "main"); err != nil {
		return nil, err
	}
	if err := g.write(files); err != nil {
		return nil, err
	}
	if _, err := g.commit(author{"stress", "stress@example.com"}, "Initial commit"); err != nil {
		return nil, err
	}
	if _, err := g.git(nil, "push", "-q", g.url, "HEAD:refs/heads/main"); err != nil {
		return nil, err
	}
	return g, nil
}

// write writes files into the working tree and stages them. An empty
// content deletes the file.
func (g *gitRepo) write(files map[string]string) error {
	for name, content := range files {
		p := filepath.Join(g.dir, name)
		if content == "" {
			if err := os.Remove(p); err != nil && !os.IsNotExist(err) {
				return err
			}
			continue
		}
		if err := os.MkdirAll(filepath.Dir(p), 0o755); err != nil {
			return err
		}
		if err := os.WriteFile(p, []byte(content), 0o644); err != nil {
			return err
		}
	}
	_, err := g.git(nil, "add", "-A")
	return err
}

func (g *gitRepo) commit(a author, msg string) (string, error) {
	if _, err := g.git(authorEnv(a), "commit", "-q", "--allow-empty", "-m", msg); err != nil {
		return "", err
	}
	return g.git(nil, "rev-parse", "HEAD")
}

// fetch fetches main and the given branches from the git server into
// refs/remotes/origin/, and returns their heads, "" for a branch that the
// server doesn't have.
func (g *gitRepo) fetch(branches ...string) (map[string]string, error) {
	refs := map[string]string{}
	out, err := g.git(nil, "ls-remote", g.url)
	if err != nil {
		return nil, err
	}
	for line := range strings.SplitSeq(out, "\n") {
		sha, ref, ok := strings.Cut(line, "\t")
		if ok {
			refs[strings.TrimPrefix(ref, "refs/heads/")] = sha
		}
	}
	args := []string{"fetch", "-q", g.url}
	heads := map[string]string{}
	for _, b := range append([]string{"main"}, branches...) {
		heads[b] = refs[b]
		if refs[b] != "" {
			args = append(args, "+refs/heads/"+b+":refs/remotes/origin/"+b)
		}
	}
	if _, err := g.git(nil, args...); err != nil {
		return nil, err
	}
	return heads, nil
}

// push pushes HEAD to branch and returns when the git server has it.
func (g *gitRepo) push(branch string) error {
	_, err := g.git(nil, "push", "-q", g.url, "HEAD:refs/heads/"+branch)
	return err
}

// tree returns the files of commit, by path.
func (g *gitRepo) tree(commit string) (map[string]string, error) {
	out, err := g.git(nil, "ls-tree", "-r", "--name-only", commit)
	if err != nil {
		return nil, err
	}
	files := map[string]string{}
	for name := range strings.SplitSeq(out, "\n") {
		if name == "" {
			continue
		}
		content, err := g.git(nil, "show", commit+":"+name)
		if err != nil {
			return nil, err
		}
		files[name] = content
	}
	return files, nil
}

// retry runs f until it succeeds, up to attempts times, a second apart.
func retry(attempts int, f func() error) error {
	var err error
	for i := range attempts {
		if err = f(); err == nil {
			return nil
		}
		if i < attempts-1 {
			time.Sleep(time.Second)
		}
	}
	return err
}
