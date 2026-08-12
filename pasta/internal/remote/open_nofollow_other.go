//go:build !unix

package remote

import (
	"fmt"
	"os"
)

// openNoFollow approximates O_NOFOLLOW on platforms that lack it:
// Lstat and refuse symlinks, then open. Still races, but remote
// modules are written by us into a private cache directory.
func openNoFollow(p string) (*os.File, error) {
	info, err := os.Lstat(p)
	if err != nil {
		return nil, err
	}
	if info.Mode()&os.ModeSymlink != 0 {
		return nil, fmt.Errorf("%s: symlinks are not allowed in remote modules", p)
	}
	return os.Open(p)
}
