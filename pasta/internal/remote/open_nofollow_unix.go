//go:build unix

package remote

import (
	"os"
	"syscall"
)

// openNoFollow opens p for reading without following a final-path
// symlink (O_NOFOLLOW). Used when hashing remote-module files after
// WalkDir has already rejected ModeSymlink entries, closing the
// TOCTOU window where a symlink could be swapped in.
func openNoFollow(p string) (*os.File, error) {
	return os.OpenFile(p, os.O_RDONLY|syscall.O_NOFOLLOW, 0)
}
