package git

import (
	"context"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"unicode"
)

// MergeOptions changes how Merge merges.
type MergeOptions struct {
	// Base is the merge base to use. Merge finds one when it's empty.
	Base string
	// Union lists path patterns, in the gitattributes format, whose
	// conflicting lines Merge keeps from both sides instead of marking them
	// as conflicts.
	Union []string
}

// Conflict is a file that Merge couldn't merge, as it is in the merge base
// and on each side. A version is nil where the file doesn't exist.
type Conflict struct {
	Path               string
	Base, Ours, Theirs *TreeEntry
}

// Merge merges theirs into ours without a worktree. It returns the merged
// tree, which holds each conflicted text file with diff3-style conflict
// markers labeled with ours, o.Base, and theirs, and the files that
// conflict. Attributes from the commits' .gitattributes files don't apply,
// so a branch can't choose how its own conflicts merge.
func (r *Repo) Merge(ctx context.Context, ours, theirs string, o MergeOptions) (tree string, conflicts []Conflict, err error) {
	noAttrs, err := r.noAttributes(ctx)
	if err != nil {
		return "", nil, err
	}
	args := []string{noAttrs, "-c", "merge.conflictStyle=diff3"}
	if len(o.Union) > 0 {
		attrs, err := UnionAttributes(o.Union)
		if err != nil {
			return "", nil, err
		}
		file := filepath.Join(r.Dir, fmt.Sprintf("git-k8s-%d.attributes", indexes.Add(1)))
		if err := os.WriteFile(file, []byte(attrs), 0o644); err != nil {
			return "", nil, err
		}
		defer os.Remove(file)
		args = append(args, "-c", "core.attributesFile="+file)
	}
	args = append(args, "merge-tree", "--write-tree", "-z", "--no-messages")
	if o.Base != "" {
		args = append(args, "--merge-base="+o.Base)
	}
	res, err := r.git.exec(ctx, r.Dir, append(args, "--end-of-options", ours, theirs), opts{})
	if err != nil {
		return "", nil, err
	}
	fields := strings.Split(strings.TrimSuffix(string(res.stdout), "\x00"), "\x00")
	if (res.code != 0 && res.code != 1) || fields[0] == "" {
		return "", nil, &Error{Command: "merge-tree", Code: res.code, Stderr: res.stderr}
	}
	index := map[string]int{}
	for _, f := range fields[1:] {
		meta, path, ok := strings.Cut(f, "\t")
		m := strings.Fields(meta)
		if !ok || len(m) != 3 {
			return "", nil, fmt.Errorf("git merge-tree: unexpected output %q", f)
		}
		i, seen := index[path]
		if !seen {
			i = len(conflicts)
			index[path] = i
			conflicts = append(conflicts, Conflict{Path: path})
		}
		e := &TreeEntry{Mode: m[0], Type: "blob", SHA: m[1], Path: path}
		if e.Mode == "160000" {
			e.Type = "commit"
		}
		switch m[2] {
		case "1":
			conflicts[i].Base = e
		case "2":
			conflicts[i].Ours = e
		case "3":
			conflicts[i].Theirs = e
		}
	}
	if res.code == 1 && len(conflicts) == 0 {
		return "", nil, fmt.Errorf("git merge-tree reported conflicts in %s and %s without listing any", ours, theirs)
	}
	return fields[0], conflicts, nil
}

// noAttributes returns the option that makes git read attributes from the
// empty tree. Without it, git reads them from the tree that attr.tree names
// or, in some versions such as 2.43, from HEAD in a bare repository.
func (r *Repo) noAttributes(ctx context.Context) (string, error) {
	empty, err := r.git.run(ctx, r.Dir, []string{"hash-object", "-t", "tree", "--stdin"}, opts{stdin: []byte{}})
	return "--attr-source=" + strings.TrimSpace(string(empty)), err
}

// UnionAttributes returns a gitattributes file that sets merge=union for
// each pattern. It rejects patterns that the file can't hold.
func UnionAttributes(patterns []string) (string, error) {
	var b strings.Builder
	for _, p := range patterns {
		if p == "" || strings.HasPrefix(p, "!") || strings.HasPrefix(p, "#") || strings.HasPrefix(p, "[attr]") ||
			strings.ContainsFunc(p, func(c rune) bool { return c == '"' || unicode.IsSpace(c) || unicode.IsControl(c) }) {
			return "", fmt.Errorf("%q isn't a path pattern that git can union-merge", p)
		}
		fmt.Fprintf(&b, "%s merge=union\n", p)
	}
	return b.String(), nil
}

// MergeBases returns every best common ancestor of two commits. A merge of
// commits with more than one depends on how git combines them.
func (r *Repo) MergeBases(ctx context.Context, a, b string) ([]string, error) {
	res, err := r.git.exec(ctx, r.Dir, []string{"merge-base", "--all", "--end-of-options", a, b}, opts{})
	switch {
	case err != nil:
		return nil, err
	case res.code == 0:
		return strings.Fields(string(res.stdout)), nil
	case res.code == 1:
		return nil, nil
	}
	return nil, &Error{Command: "merge-base", Code: res.code, Stderr: res.stderr}
}

// FetchRef fetches one ref from the remote and returns the commit that it
// points to. It keeps a branch under refs/remotes/origin/, as Fetch does,
// and any other ref under its own name.
func (r *Repo) FetchRef(ctx context.Context, remote Remote, ref string) (string, error) {
	if !strings.HasPrefix(ref, "refs/") {
		return "", fmt.Errorf("%q isn't a full ref name", ref)
	}
	// check-ref-format takes no --end-of-options, and the refs/ prefix
	// keeps ref from reading as an option.
	if _, err := r.run(ctx, "check-ref-format", ref); err != nil {
		return "", fmt.Errorf("%q isn't a full ref name", ref)
	}
	local := ref
	if b, ok := strings.CutPrefix(ref, "refs/heads/"); ok {
		local = "refs/remotes/origin/" + b
	}
	args := []string{"fetch", "--quiet", "--no-tags", "--no-write-fetch-head", "--end-of-options", remote.URL, "+" + ref + ":" + local}
	if _, err := r.git.run(ctx, r.Dir, args, opts{auth: remote.Auth}); err != nil {
		return "", err
	}
	return r.text(ctx, "rev-parse", "--verify", "--end-of-options", local+"^{commit}")
}
