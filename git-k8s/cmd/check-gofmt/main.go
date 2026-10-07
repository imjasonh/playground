// Command check-gofmt checks that a branch's Go files are formatted.
//
// The gofmt check formats every .go file in the branch's head with
// go/format, the same formatting as gofmt, and skips files under vendor and
// testdata directories. If any file changes, it commits the formatted files
// on top of the head and pushes the commit if the merge policy lets it. A
// file that doesn't parse fails the check. So does a file larger than
// 8 MiB, and a head whose list of files from git ls-tree is larger than
// 16 MiB, about 150,000 files, because the check doesn't read that much.
package main

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"go/format"
	"slices"
	"strings"
	"sync"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/mirror"
	"github.com/imjasonh/playground/git-k8s/signing"
	"github.com/imjasonh/playground/kube"
)

// Branch is this check's view of a GitBranch.
type Branch struct {
	kube.Object `kube:"apiVersion=git-k8s.imjasonh.com/v1alpha1,kind=GitBranch,plural=gitbranches,scope=Namespaced"`
	Spec        gitk8s.GitBranchSpec `json:"spec"`
	Status      struct {
		Checks struct {
			Result *gitk8s.CheckResult `json:"gofmt,omitempty"`
		} `json:"checks,omitzero"`
	} `json:"status,omitzero"`
}

func (b *Branch) Parts() (*kube.ObjectMeta, *gitk8s.GitBranchSpec, **gitk8s.CheckResult) {
	return &b.ObjectMeta, &b.Spec, &b.Status.Checks.Result
}

var check = checks.Check{Name: "gofmt", FilesOnly: true, Remote: mirror.Remote, SigningKey: signing.Key, Run: run}

// formatted holds the SHAs of blobs that are already formatted. A blob's
// formatting never changes, so later runs skip reading it.
var formatted = &shaSet{max: 1 << 15}

func run(ctx context.Context, in *checks.Input) (checks.Verdict, error) {
	repo, err := in.Repo(ctx)
	if err != nil {
		return checks.Verdict{}, err
	}
	head := in.Spec.Head
	entries, err := repo.LsTree(ctx, head)
	switch {
	case errors.Is(err, git.ErrTooBig):
		return checks.Fail("can't list the files in %s: the list is larger than %d MiB, more than check-gofmt reads", gitk8s.Short(head), git.MaxTreeBytes>>20), nil
	case err != nil:
		return checks.Verdict{}, err
	}
	var files []git.TreeEntry
	var unknown []string
	for _, e := range entries {
		if isGo(e) {
			files = append(files, e)
			if !formatted.has(e.SHA) {
				unknown = append(unknown, e.SHA)
			}
		}
	}
	sizes, err := repo.BlobSizes(ctx, unknown)
	if err != nil {
		return checks.Verdict{}, err
	}
	var fixes []git.TreeEntry
	var changed, broken []string
	// A tree can list one blob many times, so done formats each blob once.
	done := map[string]formatting{}
	for _, e := range files {
		f, ok := done[e.SHA]
		if !ok {
			if f, err = gofmt(ctx, repo, e.SHA, sizes); err != nil {
				return checks.Verdict{}, err
			}
			done[e.SHA] = f
		}
		switch {
		case f.tooBig:
			broken = append(broken, fmt.Sprintf("%s is larger than %d MiB, more than check-gofmt reads", e.Path, git.MaxBlobBytes>>20))
		case f.err != nil:
			broken = append(broken, fmt.Sprintf("can't parse %s: %v", e.Path, f.err))
		case f.sha != e.SHA:
			fixes = append(fixes, git.TreeEntry{Mode: e.Mode, SHA: f.sha, Path: e.Path})
			changed = append(changed, e.Path)
		}
	}
	total := len(files)
	if len(broken) > 0 {
		return checks.Fail("%s", strings.Join(broken, "; ")), nil
	}
	if len(fixes) == 0 {
		return checks.Pass("%d Go files are formatted", total), nil
	}
	c, err := repo.Commit(ctx, head)
	if err != nil {
		return checks.Verdict{}, err
	}
	tree, err := repo.ReplaceFiles(ctx, c.Tree, fixes)
	if err != nil {
		return checks.Verdict{}, err
	}
	msg := fmt.Sprintf("Format Go files with gofmt\n\n%s\n\n%s: gofmt\n", strings.Join(changed, "\n"), git.FixerTrailer)
	fix, err := in.CommitTree(ctx, tree, []string{head}, msg, c.Time)
	if err != nil {
		return checks.Verdict{}, err
	}
	v := checks.Fail("%d of %d Go files need gofmt: %s", len(changed), total, strings.Join(changed, ", "))
	v.Outputs = map[string]string{"files": strings.Join(changed, ",")}
	v.Fix = fix
	return v, nil
}

// formatting is what gofmt makes of a blob: sha is the formatted blob,
// which is the same blob if it's already formatted. tooBig or err says why
// gofmt can't format the blob.
type formatting struct {
	sha    string
	tooBig bool
	err    error
}

// gofmt formats the blob sha. sizes holds the size of each blob that
// formatted didn't hold when the run started.
func gofmt(ctx context.Context, repo *git.Repo, sha string, sizes map[string]int64) (formatting, error) {
	size, ok := sizes[sha]
	switch {
	case !ok:
		return formatting{sha: sha}, nil
	case size > git.MaxBlobBytes:
		return formatting{tooBig: true}, nil
	}
	src, err := repo.ReadBlob(ctx, sha)
	if err != nil {
		return formatting{}, err
	}
	out, err := format.Source(src)
	switch {
	case err != nil:
		return formatting{err: err}, nil
	case bytes.Equal(out, src):
		formatted.add(sha)
		return formatting{sha: sha}, nil
	}
	fixed, err := repo.WriteBlob(ctx, out)
	return formatting{sha: fixed}, err
}

// shaSet is a set of SHAs that holds at most 2*max of them. It keeps two
// generations: when the newer one holds max SHAs, the older one goes and
// the newer one becomes the older. has moves a SHA that it finds in the
// older generation to the newer one, so the SHAs that runs keep finding
// stay. It's safe for concurrent use.
type shaSet struct {
	max int

	mu       sync.Mutex
	cur, old map[string]struct{}
}

func (s *shaSet) has(sha string) bool {
	s.mu.Lock()
	defer s.mu.Unlock()
	if _, ok := s.cur[sha]; ok {
		return true
	}
	_, ok := s.old[sha]
	if ok {
		s.addLocked(sha)
	}
	return ok
}

func (s *shaSet) add(sha string) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.addLocked(sha)
}

func (s *shaSet) addLocked(sha string) {
	if len(s.cur) >= s.max {
		s.old, s.cur = s.cur, nil
	}
	if s.cur == nil {
		s.cur = map[string]struct{}{}
	}
	// A SHA from LsTree is part of the string that holds the whole list, so
	// the set keeps a copy, not the list.
	s.cur[strings.Clone(sha)] = struct{}{}
}

// isGo reports whether gofmt applies to a tree entry: a regular .go file
// outside vendor and testdata directories.
func isGo(e git.TreeEntry) bool {
	if e.Type != "blob" || (e.Mode != "100644" && e.Mode != "100755") || !strings.HasSuffix(e.Path, ".go") {
		return false
	}
	dirs := strings.Split(e.Path, "/")
	return !slices.ContainsFunc(dirs[:len(dirs)-1], func(d string) bool { return d == "vendor" || d == "testdata" })
}

func main() { checks.Main[Branch](check) }
