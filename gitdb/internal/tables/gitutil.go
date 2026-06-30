package tables

import (
	"bytes"
	"fmt"
	"io"

	"github.com/go-git/go-git/v5/plumbing"
	"github.com/go-git/go-git/v5/plumbing/object"

	"github.com/imjasonh/playground/gitdb/internal/gitrepo"
)

// startCommit resolves the commit at which a scan should begin. An empty ref
// means HEAD; otherwise ref is resolved as a revision (branch, tag, short or
// full hash, etc.). It also returns the label to report for the hidden `ref`
// column.
func startCommit(repo *gitrepo.Repo, ref string) (*object.Commit, string, error) {
	g := repo.Git()
	if ref == "" || ref == "HEAD" {
		head, err := g.Head()
		if err != nil {
			return nil, "", fmt.Errorf("resolve HEAD: %w", err)
		}
		c, err := g.CommitObject(head.Hash())
		if err != nil {
			return nil, "", err
		}
		return c, "HEAD", nil
	}
	h, err := g.ResolveRevision(plumbing.Revision(ref))
	if err != nil {
		return nil, "", fmt.Errorf("resolve revision %q: %w", ref, err)
	}
	c, err := g.CommitObject(*h)
	if err != nil {
		return nil, "", err
	}
	return c, ref, nil
}

// blobBytes reads the full contents of a blob, capping at max bytes (max <= 0
// reads everything).
func blobBytes(repo *gitrepo.Repo, h plumbing.Hash, max int64) ([]byte, error) {
	blob, err := repo.Git().BlobObject(h)
	if err != nil {
		return nil, err
	}
	r, err := blob.Reader()
	if err != nil {
		return nil, err
	}
	defer r.Close()
	if max > 0 {
		return io.ReadAll(io.LimitReader(r, max))
	}
	return io.ReadAll(r)
}

// looksBinary applies git's heuristic: a NUL byte in the first 8000 bytes means
// the content is binary.
func looksBinary(b []byte) bool {
	n := len(b)
	if n > 8000 {
		n = 8000
	}
	return bytes.IndexByte(b[:n], 0) >= 0
}
