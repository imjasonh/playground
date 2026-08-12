package main

import (
	"fmt"
	"os"
	"path/filepath"
)

// writeFixedFile atomically replaces path with data when path is a
// regular (non-symlink) file.
//
// Using a same-directory temp + rename avoids:
//   - following a symlink and rewriting an outside target
//   - leaving a truncated file if the process dies mid-write
// and preserves the original permission bits.
func writeFixedFile(path string, data []byte) error {
	info, err := os.Lstat(path)
	if err != nil {
		return err
	}
	if info.Mode()&os.ModeSymlink != 0 {
		return fmt.Errorf("refusing to write through symlink")
	}
	if !info.Mode().IsRegular() {
		return fmt.Errorf("refusing to write non-regular file")
	}
	dir := filepath.Dir(path)
	tmp, err := os.CreateTemp(dir, ".pasta-fix-*")
	if err != nil {
		return err
	}
	tmpName := tmp.Name()
	cleanup := true
	defer func() {
		if cleanup {
			_ = os.Remove(tmpName)
		}
	}()
	if _, err := tmp.Write(data); err != nil {
		_ = tmp.Close()
		return err
	}
	if err := tmp.Chmod(info.Mode().Perm()); err != nil {
		_ = tmp.Close()
		return err
	}
	if err := tmp.Sync(); err != nil {
		_ = tmp.Close()
		return err
	}
	if err := tmp.Close(); err != nil {
		return err
	}
	// Re-check the destination immediately before rename so a symlink
	// swap after the initial Lstat still cannot redirect the write.
	info2, err := os.Lstat(path)
	if err != nil {
		return err
	}
	if info2.Mode()&os.ModeSymlink != 0 || !info2.Mode().IsRegular() {
		return fmt.Errorf("refusing to write: destination is no longer a regular file")
	}
	if err := os.Rename(tmpName, path); err != nil {
		return err
	}
	cleanup = false
	return nil
}
