// Package rootfs builds minimal ext4 images for SSH apps.
package rootfs

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
)

// FortuneSpec describes a fortune rootfs.
type FortuneSpec struct {
	// FortuneBin is a linux (guest) binary of cmd/fortune (preferably static).
	FortuneBin string
	// CAPub is the platform user CA public key (authorized_keys format).
	CAPub []byte
	// SizeMB is the ext4 image size (default 64).
	SizeMB int
}

// BuildFromDir creates an ext4 image at outPath and copies dir into its root
// via mkfs.ext4 -d. sizeMB defaults to 512.
func BuildFromDir(dir, outPath string, sizeMB int) error {
	if dir == "" {
		return fmt.Errorf("dir required")
	}
	st, err := os.Stat(dir)
	if err != nil {
		return err
	}
	if !st.IsDir() {
		return fmt.Errorf("dir %q is not a directory", dir)
	}
	if sizeMB <= 0 {
		sizeMB = 512
	}
	return formatExt4(outPath, sizeMB, dir)
}

// BuildFortune creates an ext4 rootfs at outPath with:
//
//	/fortune — app binary (PID 1 via kernel init=)
//	/ca.pub  — platform user CA
//
// Boot with: init=/fortune -- -listen 0.0.0.0:22 -ca /ca.pub
func BuildFortune(outPath string, spec FortuneSpec) error {
	if spec.FortuneBin == "" {
		return fmt.Errorf("FortuneBin required")
	}
	if len(spec.CAPub) == 0 {
		return fmt.Errorf("CAPub required")
	}
	if spec.SizeMB == 0 {
		spec.SizeMB = 64
	}
	if err := formatExt4(outPath, spec.SizeMB, ""); err != nil {
		return err
	}

	if err := debugfsWrite(outPath, spec.FortuneBin, "fortune", "0755"); err != nil {
		return err
	}
	caTmp, err := os.CreateTemp("", "ca-*.pub")
	if err != nil {
		return err
	}
	caPath := caTmp.Name()
	if _, err := caTmp.Write(spec.CAPub); err != nil {
		_ = caTmp.Close()
		return err
	}
	_ = caTmp.Close()
	defer os.Remove(caPath)
	return debugfsWrite(outPath, caPath, "ca.pub", "0644")
}

func formatExt4(outPath string, sizeMB int, srcDir string) error {
	if err := os.MkdirAll(filepath.Dir(outPath), 0o755); err != nil {
		return err
	}
	_ = os.Remove(outPath)

	f, err := os.Create(outPath)
	if err != nil {
		return err
	}
	if err := f.Truncate(int64(sizeMB) << 20); err != nil {
		_ = f.Close()
		return err
	}
	_ = f.Close()

	args := []string{"-F", "-b", "4096"}
	if srcDir != "" {
		args = append(args, "-d", srcDir)
	}
	args = append(args, outPath)
	if out, err := exec.Command("mkfs.ext4", args...).CombinedOutput(); err != nil {
		return fmt.Errorf("mkfs.ext4: %v\n%s", err, out)
	}
	return nil
}

func debugfsWrite(image, hostFile, guestPath, mode string) error {
	cmd := exec.Command("debugfs", "-w", "-R", fmt.Sprintf("write %s %s", hostFile, guestPath), image)
	if out, err := cmd.CombinedOutput(); err != nil {
		return fmt.Errorf("debugfs write %s: %v\n%s", guestPath, err, out)
	}
	cmd = exec.Command("debugfs", "-w", "-R", fmt.Sprintf("sif %s %s", guestPath, mode), image)
	if out, err := cmd.CombinedOutput(); err != nil {
		return fmt.Errorf("debugfs sif %s: %v\n%s", guestPath, err, out)
	}
	return nil
}

// InjectFile writes or replaces a file in an existing ext4 image via debugfs.
func InjectFile(image, hostFile, guestPath, mode string) error {
	_ = exec.Command("debugfs", "-w", "-R", fmt.Sprintf("rm %s", guestPath), image).Run()
	return debugfsWrite(image, hostFile, guestPath, mode)
}

// Clone copies a base rootfs to a per-instance path.
func Clone(base, dst string) error {
	if err := os.MkdirAll(filepath.Dir(dst), 0o755); err != nil {
		return err
	}
	in, err := os.ReadFile(base)
	if err != nil {
		return err
	}
	return os.WriteFile(dst, in, 0o644)
}
