// Package gitserver serves bare git repositories over the smart HTTP
// protocol, for tests. It runs git upload-pack and git receive-pack, creates
// a repository the first time something pushes to it, and can require HTTP
// basic authentication.
package gitserver

import (
	"bytes"
	"compress/gzip"
	"crypto/subtle"
	"errors"
	"fmt"
	"io"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"
	"sync"
)

// Server serves the bare repositories under Root, so the repository at
// Root/app.git is at URL path /app.git.
type Server struct {
	// Root holds the repositories.
	Root string
	// Username and Password, when Password is set, are the credentials
	// that every request needs.
	Username, Password string
	// AllowedSigners, when set, is the path of an allowed signers file, as
	// ssh-keygen(1) describes. The repositories that the server creates
	// then reject a push that adds a commit unless the key that the file
	// lists for the commit's committer email signed it, as a forge that
	// requires signed commits does.
	AllowedSigners string

	// mu keeps requests out of a repository until ensure has set it up.
	mu sync.Mutex
}

var repoRE = regexp.MustCompile(`^/([A-Za-z0-9][-A-Za-z0-9_.]*\.git)/(info/refs|git-upload-pack|git-receive-pack)$`)

func (s *Server) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	if s.Password != "" {
		user, pass, ok := r.BasicAuth()
		if !ok || subtle.ConstantTimeCompare([]byte(user), []byte(s.Username)) != 1 ||
			subtle.ConstantTimeCompare([]byte(pass), []byte(s.Password)) != 1 {
			w.Header().Set("WWW-Authenticate", `Basic realm="git"`)
			http.Error(w, "authentication required", http.StatusUnauthorized)
			return
		}
	}
	m := repoRE.FindStringSubmatch(r.URL.Path)
	if m == nil || strings.Contains(m[1], "..") {
		http.NotFound(w, r)
		return
	}
	dir := filepath.Join(s.Root, m[1])
	switch {
	case m[2] == "info/refs" && r.Method == http.MethodGet:
		service := r.URL.Query().Get("service")
		if service != "git-upload-pack" && service != "git-receive-pack" {
			http.Error(w, "dumb HTTP isn't supported", http.StatusForbidden)
			return
		}
		if err := s.ensure(dir, service == "git-receive-pack"); err != nil {
			http.Error(w, err.Error(), http.StatusNotFound)
			return
		}
		w.Header().Set("Content-Type", "application/x-"+service+"-advertisement")
		w.Header().Set("Cache-Control", "no-cache")
		protocol := r.Header.Get("Git-Protocol")
		if !strings.Contains(protocol, "version=2") {
			fmt.Fprintf(w, "%04x# service=%s\n0000", len(service)+15, service)
		}
		s.run(w, strings.TrimPrefix(service, "git-"), dir, protocol, nil, "--advertise-refs")
	case r.Method == http.MethodPost:
		if err := s.ensure(dir, false); err != nil {
			http.Error(w, err.Error(), http.StatusNotFound)
			return
		}
		body := io.Reader(r.Body)
		if r.Header.Get("Content-Encoding") == "gzip" {
			zr, err := gzip.NewReader(r.Body)
			if err != nil {
				http.Error(w, err.Error(), http.StatusBadRequest)
				return
			}
			defer zr.Close()
			body = zr
		}
		w.Header().Set("Content-Type", "application/x-"+m[2]+"-result")
		s.run(w, strings.TrimPrefix(m[2], "git-"), dir, r.Header.Get("Git-Protocol"), body)
	default:
		http.Error(w, "method not allowed", http.StatusMethodNotAllowed)
	}
}

// ensure makes sure dir is a repository, creating it when create is set.
func (s *Server) ensure(dir string, create bool) error {
	s.mu.Lock()
	defer s.mu.Unlock()
	if _, err := os.Stat(filepath.Join(dir, "HEAD")); err == nil {
		return nil
	}
	if !create {
		return fmt.Errorf("no repository %s", filepath.Base(dir))
	}
	err := Init(dir)
	if err == nil && s.AllowedSigners != "" {
		err = requireSignatures(dir, s.AllowedSigners)
	}
	if err != nil {
		// The check above takes any directory with a HEAD as set up.
		return errors.Join(err, os.RemoveAll(dir))
	}
	return nil
}

func (s *Server) run(w http.ResponseWriter, service, dir, protocol string, stdin io.Reader, extra ...string) {
	args := append([]string{service, "--stateless-rpc"}, extra...)
	cmd := exec.Command("git", append(args, dir)...)
	cmd.Env = append(os.Environ(), "GIT_PROTOCOL="+protocol, "GIT_CONFIG_NOSYSTEM=1", "GIT_CONFIG_GLOBAL="+os.DevNull)
	cmd.Stdin = stdin
	var stderr bytes.Buffer
	cmd.Stdout, cmd.Stderr = w, &stderr
	if err := cmd.Run(); err != nil {
		// The status line has gone out, so the client sees a truncated
		// response; log the reason for whoever runs the server.
		fmt.Fprintf(os.Stderr, "gitserver: git %s %s: %v: %s\n", service, filepath.Base(dir), err, stderr.String())
	}
}

// Init creates a bare repository at dir that lets clients fetch any commit
// by SHA. Pushes to it don't start automatic maintenance, which runs in the
// background and can still be writing to the repository when a test's
// cleanup removes it.
func Init(dir string) error {
	for _, args := range [][]string{
		{"init", "--quiet", "--bare", dir},
		{"-C", dir, "config", "uploadpack.allowAnySHA1InWant", "true"},
		{"-C", dir, "config", "receive.autoGC", "false"},
	} {
		cmd := exec.Command("git", args...)
		cmd.Env = append(os.Environ(), "GIT_CONFIG_NOSYSTEM=1", "GIT_CONFIG_GLOBAL="+os.DevNull)
		if out, err := cmd.CombinedOutput(); err != nil {
			return fmt.Errorf("git %s: %v: %s", args[0], err, out)
		}
	}
	return nil
}
