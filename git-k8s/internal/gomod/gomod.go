// Package gomod finds the go.mod files in a commit.
package gomod

import (
	"context"
	"path"
	"strings"

	"github.com/imjasonh/playground/git-k8s/internal/git"
)

// IsModFile reports whether p is the path of a go.mod file outside testdata
// and vendor directories, which hold test inputs and copies of other
// modules.
func IsModFile(p string) bool {
	dir, file := path.Split(p)
	if file != "go.mod" {
		return false
	}
	for part := range strings.SplitSeq(dir, "/") {
		if part == "testdata" || part == "vendor" {
			return false
		}
	}
	return true
}

// Files lists the go.mod files in a commit, other than symbolic links.
func Files(ctx context.Context, repo *git.Repo, commit string) ([]git.TreeEntry, error) {
	entries, err := repo.LsTree(ctx, commit)
	if err != nil {
		return nil, err
	}
	var mods []git.TreeEntry
	for _, e := range entries {
		if e.Type == "blob" && e.Mode != "120000" && IsModFile(e.Path) {
			mods = append(mods, e)
		}
	}
	return mods, nil
}
