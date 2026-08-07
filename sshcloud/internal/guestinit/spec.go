// Package guestinit execs an OCI image as microVM PID 1.
package guestinit

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"syscall"
)

const (
	// GuestBinary is the path of the trampoline inside the microVM.
	GuestBinary = "/platform-init"
	// GuestSpec is the boot spec JSON inside the microVM.
	GuestSpec = "/platform-boot.json"
)

// SpecBeside is the conventional sidecar next to an ext4 rootfs
// (`foo.ext4` → `foo.boot.json`).
func SpecBeside(rootfsPath string) string {
	ext := filepath.Ext(rootfsPath)
	base := strings.TrimSuffix(rootfsPath, ext)
	if base == "" {
		base = rootfsPath
	}
	return base + ".boot.json"
}

// Spec is the subset of OCI image config used to start PID 1.
type Spec struct {
	Entrypoint []string `json:"entrypoint"`
	Cmd        []string `json:"cmd"`
	Env        []string `json:"env"`
	WorkingDir string   `json:"workingDir"`
}

// Argv is Entrypoint followed by Cmd (Docker/OCI semantics).
func Argv(s Spec) []string {
	out := make([]string, 0, len(s.Entrypoint)+len(s.Cmd))
	out = append(out, s.Entrypoint...)
	out = append(out, s.Cmd...)
	return out
}

// Validate reports whether the spec can be exec'd.
func (s Spec) Validate() error {
	if len(Argv(s)) == 0 {
		return fmt.Errorf("boot spec has empty Entrypoint and Cmd")
	}
	if strings.TrimSpace(Argv(s)[0]) == "" {
		return fmt.Errorf("boot spec executable is empty")
	}
	return nil
}

// WriteFile writes spec as JSON.
func WriteFile(path string, s Spec) error {
	b, err := json.MarshalIndent(s, "", "  ")
	if err != nil {
		return err
	}
	return os.WriteFile(path, append(b, '\n'), 0o644)
}

// LoadFile reads a spec JSON file.
func LoadFile(path string) (Spec, error) {
	b, err := os.ReadFile(path)
	if err != nil {
		return Spec{}, err
	}
	var s Spec
	if err := json.Unmarshal(b, &s); err != nil {
		return Spec{}, fmt.Errorf("parse boot spec: %w", err)
	}
	return s, nil
}

// Run loads specPath, applies env + working dir, and execs Entrypoint+Cmd.
func Run(specPath string) {
	if specPath == "" {
		specPath = GuestSpec
	}
	spec, err := LoadFile(specPath)
	if err != nil {
		fmt.Fprintf(os.Stderr, "guestinit: %v\n", err)
		os.Exit(127)
	}
	if err := spec.Validate(); err != nil {
		fmt.Fprintf(os.Stderr, "guestinit: %v\n", err)
		os.Exit(127)
	}
	if os.Getpid() == 1 || os.Getenv("SSHCLOUD_GUESTINIT_MOUNT") == "1" {
		if err := mountRuntimeFilesystems(); err != nil {
			fmt.Fprintf(os.Stderr, "guestinit: %v\n", err)
			os.Exit(127)
		}
	}
	if err := Exec(spec); err != nil {
		fmt.Fprintf(os.Stderr, "guestinit: %v\n", err)
		os.Exit(127)
	}
}

func mountRuntimeFilesystems() error {
	type mountSpec struct {
		source, target, fs, data string
		flags                    uintptr
		optional                 bool
	}
	mounts := []mountSpec{
		{source: "proc", target: "/proc", fs: "proc", flags: syscall.MS_NOSUID | syscall.MS_NODEV | syscall.MS_NOEXEC},
		{source: "sysfs", target: "/sys", fs: "sysfs", flags: syscall.MS_RDONLY | syscall.MS_NOSUID | syscall.MS_NODEV | syscall.MS_NOEXEC, optional: true},
		{source: "devtmpfs", target: "/dev", fs: "devtmpfs", flags: syscall.MS_NOSUID},
		{source: "devpts", target: "/dev/pts", fs: "devpts", data: "newinstance,ptmxmode=0666,mode=0620", flags: syscall.MS_NOSUID | syscall.MS_NOEXEC},
	}
	for _, mount := range mounts {
		if err := os.MkdirAll(mount.target, 0o755); err != nil {
			return err
		}
		if err := syscall.Mount(mount.source, mount.target, mount.fs, mount.flags, mount.data); err != nil &&
			err != syscall.EBUSY {
			if mount.optional {
				continue
			}
			return fmt.Errorf("mount %s on %s: %w", mount.fs, mount.target, err)
		}
	}
	if err := os.MkdirAll("/tmp", 0o1777); err != nil {
		return err
	}
	if err := os.Chmod("/tmp", 0o1777); err != nil {
		return err
	}
	_ = os.Remove("/dev/ptmx")
	if err := os.Symlink("pts/ptmx", "/dev/ptmx"); err != nil && !os.IsExist(err) {
		return fmt.Errorf("link /dev/ptmx: %w", err)
	}
	return nil
}

// Exec chdirs, builds env, and syscall.Exec's the image command.
func Exec(spec Spec) error {
	argv := Argv(spec)
	env := spec.Env
	if len(env) == 0 {
		env = []string{"PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin", "HOME=/"}
	}
	if wd := strings.TrimSpace(spec.WorkingDir); wd != "" && wd != "." {
		if err := os.Chdir(wd); err != nil {
			return fmt.Errorf("chdir %q: %w", wd, err)
		}
	}
	bin := argv[0]
	resolved, err := resolveExec(bin, spec.WorkingDir, env)
	if err != nil {
		return err
	}
	return syscall.Exec(resolved, argv, env)
}

func resolveExec(bin, workingDir string, env []string) (string, error) {
	if filepath.IsAbs(bin) {
		return bin, nil
	}
	if strings.Contains(bin, string(os.PathSeparator)) {
		if workingDir != "" && !filepath.IsAbs(bin) {
			return filepath.Join(workingDir, bin), nil
		}
		return bin, nil
	}
	path := envPATH(env)
	for _, dir := range filepath.SplitList(path) {
		if dir == "" {
			dir = "."
		}
		cand := filepath.Join(dir, bin)
		if st, err := os.Stat(cand); err == nil && !st.IsDir() && st.Mode()&0o111 != 0 {
			return cand, nil
		}
	}
	return "", fmt.Errorf("executable %q not found in PATH", bin)
}

func envPATH(env []string) string {
	for _, e := range env {
		if after, ok := strings.CutPrefix(e, "PATH="); ok {
			return after
		}
	}
	return "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"
}
