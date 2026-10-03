// Command check-gofmt checks that a branch's Go files are formatted.
//
// The gofmt check formats every .go file in the branch's head with
// go/format, the same formatting as gofmt, and skips files under vendor and
// testdata directories. If any file changes, it commits the formatted files
// on top of the head and pushes the commit if the merge policy lets it. A
// file that doesn't parse fails the check.
package main

import (
	"bytes"
	"context"
	"fmt"
	"go/format"
	"slices"
	"strings"
	"sync"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/internal/git"
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

var check = checks.Check{Name: "gofmt", Run: run}

// formatted holds the SHAs of blobs that are already formatted. A blob's
// formatting never changes, so later runs skip reading it.
var formatted sync.Map

func run(ctx context.Context, in *checks.Input) (checks.Verdict, error) {
	repo, err := in.Repo(ctx)
	if err != nil {
		return checks.Verdict{}, err
	}
	head := in.Spec.Head
	entries, err := repo.LsTree(ctx, head)
	if err != nil {
		return checks.Verdict{}, err
	}
	var fixes []git.TreeEntry
	var changed, broken []string
	total := 0
	for _, e := range entries {
		if !isGo(e) {
			continue
		}
		total++
		if _, ok := formatted.Load(e.SHA); ok {
			continue
		}
		src, err := repo.ReadBlob(ctx, e.SHA)
		if err != nil {
			return checks.Verdict{}, err
		}
		out, err := format.Source(src)
		if err != nil {
			broken = append(broken, fmt.Sprintf("%s: %v", e.Path, err))
			continue
		}
		if bytes.Equal(out, src) {
			formatted.Store(e.SHA, struct{}{})
			continue
		}
		sha, err := repo.WriteBlob(ctx, out)
		if err != nil {
			return checks.Verdict{}, err
		}
		fixes = append(fixes, git.TreeEntry{Mode: e.Mode, SHA: sha, Path: e.Path})
		changed = append(changed, e.Path)
	}
	if len(broken) > 0 {
		return checks.Fail("can't parse %s", strings.Join(broken, "; ")), nil
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
	fix, err := repo.CommitTree(ctx, tree, []string{head}, msg, in.Identity, c.Time)
	if err != nil {
		return checks.Verdict{}, err
	}
	v := checks.Fail("%d of %d Go files need gofmt: %s", len(changed), total, strings.Join(changed, ", "))
	v.Outputs = map[string]string{"files": strings.Join(changed, ",")}
	v.Fix = fix
	return v, nil
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
