// Package backend resolves where to dial for an app instance.
// The local backend runs sample apps as subprocesses (pre-Firecracker).
package backend

import (
	"bufio"
	"fmt"
	"os"
	"os/exec"
	"sync"
)

// LocalFortune starts cmd/fortune with the platform CA and tracks its address.
type LocalFortune struct {
	mu      sync.Mutex
	cmdPath string
	caPub   string // path to CA public key file
	cmd     *exec.Cmd
	addr    string
}

// NewLocalFortune returns a manager. cmdPath is the fortune binary; caPubPath is the CA .pub file.
func NewLocalFortune(cmdPath, caPubPath string) *LocalFortune {
	return &LocalFortune{cmdPath: cmdPath, caPub: caPubPath}
}

// Ensure starts fortune if needed and returns its listen address.
func (l *LocalFortune) Ensure() (string, error) {
	l.mu.Lock()
	defer l.mu.Unlock()
	if l.addr != "" && l.cmd != nil && l.cmd.Process != nil {
		return l.addr, nil
	}
	if l.cmdPath == "" {
		return "", fmt.Errorf("fortune binary path not set")
	}
	cmd := exec.Command(l.cmdPath, "-listen", "127.0.0.1:0", "-ca", l.caPub)
	stdout, err := cmd.StdoutPipe()
	if err != nil {
		return "", err
	}
	cmd.Stderr = os.Stderr
	if err := cmd.Start(); err != nil {
		return "", err
	}
	br := bufio.NewReader(stdout)
	line, err := br.ReadString('\n')
	if err != nil {
		_ = cmd.Process.Kill()
		return "", fmt.Errorf("read fortune addr: %w", err)
	}
	addr := trimLine(line)
	l.cmd = cmd
	l.addr = addr
	return addr, nil
}

func trimLine(s string) string {
	for len(s) > 0 && (s[len(s)-1] == '\n' || s[len(s)-1] == '\r') {
		s = s[:len(s)-1]
	}
	return s
}

// Stop kills the subprocess.
func (l *LocalFortune) Stop() {
	l.mu.Lock()
	defer l.mu.Unlock()
	if l.cmd != nil && l.cmd.Process != nil {
		_ = l.cmd.Process.Kill()
		_, _ = l.cmd.Process.Wait()
	}
	l.cmd = nil
	l.addr = ""
}

// Addr returns the dial address for fortune (stub registry). gen/image ignored.
func (l *LocalFortune) Addr(user, app, gen, image string) (string, error) {
	_ = user
	_ = gen
	_ = image
	if app != "fortune" {
		return "", fmt.Errorf("local backend only supports fortune, got %q", app)
	}
	return l.Ensure()
}
