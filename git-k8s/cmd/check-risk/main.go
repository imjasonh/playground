// Command check-risk rates how risky a branch's change is.
//
// The risk check compares the branch's head with its merge base on the
// parent. A change is high risk when any of these is true:
//
//   - It changes more lines than -max-lines. Lines in go.sum and go.work.sum
//     files don't count, because they're checksums that the go command
//     checks, and the versions that they cover show in go.mod.
//   - It changes a file that git treats as binary, such as one with a NUL
//     byte in its first 8,000 bytes, because git counts no lines in such a
//     file.
//   - It touches a path that matches a -sensitive glob.
//   - A go.mod file that it changes requires a module that no go.mod file
//     at the merge base requires, moves a module to an earlier version than
//     the file required, to another major version, or to a version that
//     isn't a release, replaces a module with another module or with a
//     directory outside the repository, stops replacing one, or changes the
//     go, toolchain, or godebug lines. For a new go.mod file, the check
//     compares those lines with the ones in the go.mod file of the module
//     that its directory was in at the merge base, or with no lines if the
//     directory was in no module. Modules that the file replaces with a
//     directory in the repository are the repository's own, so requiring
//     them is fine. A module that a go.mod file declares isn't, unless the
//     file replaces it, because the go command downloads it.
//   - A go.mod file replaces a module with a directory whose path goes
//     through a symbolic link or a submodule, and the change adds the
//     replacement, or adds or changes the link. The go command follows the
//     link, which can point outside the repository, and a submodule's files
//     come from another repository, so that directory isn't in the
//     repository.
//   - It adds or changes a submodule, whose files come from another
//     repository, or changes the .gitmodules file, which names that
//     repository.
//   - It changes a go.work file, whose directives apply to every module in
//     the workspace.
//   - It has commits from AI agents, which carry the Git-K8s-Agent trailer.
//
// Otherwise it's low risk, so a patch or minor release of a module that the
// repository already requires is low risk. The check always passes and
// reports the rating in its outputs, so a merge gate decides what to do with
// it:
//
//	when: checks.risk.outputs.level == "low" || checks.approval.passed
//
// The check rates each change once. The rating holds when the parent moves,
// and for a merge of the parent, a rebase, or a squash that makes the same
// change. A rating that reads go.mod files at the merge base holds only for
// the parent's head, so the check rates such a change again when the parent
// moves.
package main

import (
	"cmp"
	"context"
	"flag"
	"fmt"
	"maps"
	"path"
	"slices"
	"strconv"
	"strings"

	"golang.org/x/mod/modfile"
	"golang.org/x/mod/module"
	"golang.org/x/mod/semver"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gomod"
	"github.com/imjasonh/playground/git-k8s/mirror"
	"github.com/imjasonh/playground/kube"
)

// Branch is this check's view of a GitBranch.
type Branch struct {
	kube.Object `kube:"apiVersion=git-k8s.imjasonh.com/v1alpha1,kind=GitBranch,plural=gitbranches,scope=Namespaced"`
	Spec        gitk8s.GitBranchSpec `json:"spec"`
	Status      struct {
		Checks struct {
			Result *gitk8s.CheckResult `json:"risk,omitempty"`
		} `json:"checks,omitzero"`
	} `json:"status,omitzero"`
}

func (b *Branch) Parts() (*kube.ObjectMeta, *gitk8s.GitBranchSpec, **gitk8s.CheckResult) {
	return &b.ObjectMeta, &b.Spec, &b.Status.Checks.Result
}

var (
	maxLines  = flag.Int("max-lines", 200, "changed lines above which a change is high risk, not counting go.sum files")
	sensitive = flag.String("sensitive", "", "comma-separated globs of paths that make a change high risk, such as auth/**,**/*.pem")
)

// The check also reads whether a commit has the agent trailer. A squash
// landing keeps every such line, and a rebase keeps each copied commit's
// message, so the check can be FilesOnly. Its message doesn't count those
// commits, because a squash makes one commit of them.
//
// A rating is for the change, so the check sets SameChange. A rating that
// reads go.mod files at the merge base sets UsesParent, because those files
// can differ at another merge base where the change is the same.
var check = checks.Check{Name: "risk", SameChange: true, FilesOnly: true, Remote: mirror.Remote, Run: run}

func run(ctx context.Context, in *checks.Input) (checks.Verdict, error) {
	repo, err := in.Repo(ctx)
	if err != nil {
		return checks.Verdict{}, err
	}
	base, err := in.MergeBase(ctx)
	if err != nil {
		return checks.Verdict{}, err
	}
	if base == "" {
		v := checks.Pass("risk is high: %s has no history in common with %s", in.Spec.Branch, in.Spec.Parent)
		v.Outputs = map[string]string{"level": "high"}
		return v, nil
	}
	stats, err := repo.Numstat(ctx, base, in.Spec.Head)
	if err != nil {
		return checks.Verdict{}, err
	}
	links, err := readLinks(ctx, repo, in.Spec.Head)
	if err != nil {
		return checks.Verdict{}, err
	}
	lines, sums, gitmodules := 0, false, false
	var hits, binaries, submodules, works []string
	for _, s := range stats {
		if name := path.Base(s.Path); name == "go.sum" || name == "go.work.sum" {
			sums = true
		} else {
			lines += max(s.Added, 0) + max(s.Removed, 0)
		}
		if s.Added < 0 || s.Removed < 0 {
			binaries = append(binaries, s.Path)
		}
		switch {
		case s.Path == ".gitmodules":
			gitmodules = true
		case links[s.Path] == "submodule":
			submodules = append(submodules, s.Path)
		}
		if path.Base(s.Path) == "go.work" {
			works = append(works, s.Path)
		}
		for p := range strings.SplitSeq(*sensitive, ",") {
			if p = strings.TrimSpace(p); p != "" && gitk8s.Match(p, s.Path) {
				hits = append(hits, s.Path)
				break
			}
		}
	}
	var reasons []string
	if lines > *maxLines {
		reasons = append(reasons, fmt.Sprintf("changes %d lines, more than %d", lines, *maxLines))
	}
	if len(binaries) > 0 {
		reasons = append(reasons, "changes binary files "+strings.Join(binaries, ", "))
	}
	if len(hits) > 0 {
		reasons = append(reasons, "touches "+strings.Join(hits, ", "))
	}
	r, readBase, err := moduleReasons(ctx, repo, base, in.Spec.Head, stats, links)
	if err != nil {
		return checks.Verdict{}, err
	}
	reasons = append(reasons, r...)
	if gitmodules {
		reasons = append(reasons, "changes .gitmodules")
	}
	if len(submodules) > 0 {
		reasons = append(reasons, "changes submodules "+strings.Join(submodules, ", "))
	}
	if len(works) > 0 {
		reasons = append(reasons, "changes "+strings.Join(works, ", "))
	}
	switch n, err := repo.CountCommits(ctx, base, in.Spec.Head, git.AgentTrailer); {
	case err != nil:
		return checks.Verdict{}, err
	case n > 0:
		reasons = append(reasons, "has changes from AI agents")
	}
	level := "low"
	if len(reasons) > 0 {
		level = "high"
	} else {
		summary := fmt.Sprintf("changes %d lines in %d files", lines, len(stats))
		if sums {
			summary += ", not counting go.sum"
		}
		reasons = []string{summary}
	}
	v := checks.Pass("risk is %s: %s", level, strings.Join(reasons, "; "))
	v.Outputs = map[string]string{"level": level, "lines": strconv.Itoa(lines), "files": strconv.Itoa(len(stats))}
	v.UsesParent = readBase
	return v, nil
}

// modFile is a go.mod file, or why it can't be parsed.
type modFile struct {
	path string
	file *modfile.File
	err  error
}

// readModFiles parses the go.mod files in a commit.
func readModFiles(ctx context.Context, repo *git.Repo, commit string) ([]modFile, error) {
	entries, err := gomod.Files(ctx, repo, commit)
	if err != nil {
		return nil, err
	}
	var files []modFile
	for _, e := range entries {
		data, err := repo.ReadBlob(ctx, e.SHA)
		if err != nil {
			return nil, err
		}
		f, err := modfile.Parse(e.Path, data, nil)
		files = append(files, modFile{path: e.Path, file: f, err: err})
	}
	return files, nil
}

// readLinks maps the path of each symbolic link and submodule in a commit to
// which of the two it is.
func readLinks(ctx context.Context, repo *git.Repo, commit string) (map[string]string, error) {
	entries, err := repo.LsTree(ctx, commit)
	if err != nil {
		return nil, err
	}
	links := map[string]string{}
	for _, e := range entries {
		switch e.Mode {
		case "120000":
			links[e.Path] = "symbolic link"
		case "160000":
			links[e.Path] = "submodule"
		}
	}
	return links, nil
}

// moduleReasons says what makes the changes in stats to go.mod files, and to
// the symbolic links that their replacements go through, high risk. links
// holds the symbolic links and submodules at head, from readLinks. It
// compares each changed go.mod file with every go.mod file at base, so a
// module that another part of the repository required isn't new. It reads
// the files at base only for a change to a go.mod file or a symbolic link,
// and reports whether it did.
func moduleReasons(ctx context.Context, repo *git.Repo, base, head string, stats []git.FileStat, links map[string]string) (reasons []string, readBase bool, err error) {
	var paths []string
	changedLinks := map[string]bool{}
	for _, s := range stats {
		if gomod.IsModFile(s.Path) {
			paths = append(paths, s.Path)
		}
		if links[s.Path] == "symbolic link" {
			changedLinks[s.Path] = true
		}
	}
	if len(paths) == 0 && len(changedLinks) == 0 {
		return nil, false, nil
	}
	before, err := readModFiles(ctx, repo, base)
	if err != nil {
		return nil, true, err
	}
	after, err := readModFiles(ctx, repo, head)
	if err != nil {
		return nil, true, err
	}
	// required holds the versions of each module that the repository
	// requires, and replaced the replacements that it makes, before the
	// change. previous holds each go.mod file at base, or nil for one that
	// check-risk can't read.
	required := map[string][]string{}
	replaced := map[string]bool{}
	previous := map[string]*modfile.File{}
	for _, f := range before {
		previous[f.path] = f.file
		if f.file == nil {
			continue
		}
		for _, r := range f.file.Require {
			required[r.Mod.Path] = append(required[r.Mod.Path], r.Mod.Version)
		}
		for _, r := range f.file.Replace {
			replaced[replacement(f.path, r)] = true
		}
	}
	// majors maps a module path without its major version suffix to the
	// first such path that the repository required.
	majors := map[string]string{}
	for _, p := range slices.Sorted(maps.Keys(required)) {
		prefix, _, _ := module.SplitPathVersion(p)
		if _, ok := majors[prefix]; !ok {
			majors[prefix] = p
		}
	}

	add := func(format string, args ...any) {
		if r := fmt.Sprintf(format, args...); !slices.Contains(reasons, r) {
			reasons = append(reasons, r)
		}
	}
	for _, f := range after {
		if !slices.Contains(paths, f.path) {
			continue
		}
		if f.err != nil {
			add("changes %s, which check-risk can't read: %v", f.path, f.err)
			continue
		}
		old := previous[f.path]
		was := map[string]string{}
		if old != nil {
			for _, r := range old.Require {
				if semver.Compare(r.Mod.Version, was[r.Mod.Path]) > 0 {
					was[r.Mod.Path] = r.Mod.Version
				}
			}
		}
		for _, r := range f.file.Require {
			p, v := r.Mod.Path, r.Mod.Version
			versions := required[p]
			prefix, _, _ := module.SplitPathVersion(p)
			switch {
			case semver.Compare(v, was[p]) < 0:
				add("downgrades %s from %s to %s", p, was[p], v)
			case replacedInRepo(f, links, p, v) || slices.Contains(versions, v):
			case len(versions) == 0 && majors[prefix] != "":
				add("moves %s to %s", majors[prefix], p)
			case len(versions) == 0:
				add("adds module %s", p)
			case semver.Prerelease(v) != "":
				add("moves %s to %s, which isn't a release", p, v)
			case !slices.ContainsFunc(versions, func(old string) bool { return semver.Major(old) == semver.Major(v) }):
				add("moves %s to %s, a new major version", p, v)
			}
		}
		now := map[string]bool{}
		for _, r := range f.file.Replace {
			key := replacement(f.path, r)
			now[key] = true
			_, inRepo := replaceDir(f.path, r)
			switch {
			case replaced[key]:
			case r.New.Version != "":
				add("replaces %s with %s", r.Old, r.New)
			case !inRepo:
				add("replaces %s with %s, which is outside the repository", r.Old, r.New.Path)
			}
		}
		if old != nil {
			for _, r := range old.Replace {
				if !now[replacement(f.path, r)] {
					add("stops replacing %s with %s", r.Old, r.New)
				}
			}
		}
		heldPath, held := heldBy(previous, f.path)
		prior := func(line string) string {
			if line = cmp.Or(line, "none"); heldPath != f.path && held != nil {
				line += " in " + heldPath
			}
			return line
		}
		if a, b := goLine(held), goLine(f.file); a != b {
			add("changes the go line in %s from %s to %s", f.path, prior(a), cmp.Or(b, "none"))
		}
		if a, b := toolchainLine(held), toolchainLine(f.file); a != b {
			add("changes the toolchain line in %s from %s to %s", f.path, prior(a), cmp.Or(b, "none"))
		}
		if a, b := godebugLines(held), godebugLines(f.file); a != b {
			add("changes the godebug lines in %s from %s to %s", f.path, prior(a), cmp.Or(b, "none"))
		}
	}
	for _, f := range after {
		if f.file == nil {
			continue
		}
		for _, r := range f.file.Replace {
			dir, inRepo := replaceDir(f.path, r)
			link, kind := linkOn(dir, links)
			switch {
			case !inRepo || link == "":
			case !replaced[replacement(f.path, r)]:
				add("replaces %s with %s, which goes through the %s %s", r.Old, r.New.Path, kind, link)
			case changedLinks[link]:
				add("changes the %s %s, which a replacement of %s goes through", kind, link, r.Old)
			}
		}
	}
	return reasons, true, nil
}

// replacement returns a replace directive in the go.mod file at file as a
// string, with a directory as replaceDir returns it, so that the same
// directive in two directories differs.
func replacement(file string, r *modfile.Replace) string {
	if r.New.Version != "" {
		return r.Old.String() + " => " + r.New.String()
	}
	dir, _ := replaceDir(file, r)
	return r.Old.String() + " => " + dir
}

// replaceDir returns the directory, from the repository's root, that a
// replace directive in the go.mod file at file points to, and reports
// whether it's in the repository. A directive that names a module has no
// directory.
func replaceDir(file string, r *modfile.Replace) (dir string, inRepo bool) {
	p := r.New.Path
	switch {
	case r.New.Version != "":
		return "", false
	case path.IsAbs(p) || len(p) > 1 && p[1] == ':':
		// modfile reads a path that starts with a drive letter, such as
		// C:/mods, as a directory.
		return p, false
	}
	dir = path.Join(path.Dir(file), p)
	if dir == ".." || strings.HasPrefix(dir, "../") {
		return dir, false
	}
	return "./" + dir, true
}

// linkOn returns the symbolic link or submodule in links that dir, a
// directory in the repository from replaceDir, goes through, and which of
// the two it is.
func linkOn(dir string, links map[string]string) (link, kind string) {
	dir = strings.TrimPrefix(dir, "./")
	for i := range len(dir) + 1 {
		if i == len(dir) || dir[i] == '/' {
			if kind := links[dir[:i]]; kind != "" {
				return dir[:i], kind
			}
		}
	}
	return "", ""
}

// replacedInRepo reports whether f replaces mod at version with a directory
// in the repository whose path doesn't go through a symbolic link or a
// submodule in links.
func replacedInRepo(f modFile, links map[string]string, mod, version string) bool {
	return slices.ContainsFunc(f.file.Replace, func(r *modfile.Replace) bool {
		dir, inRepo := replaceDir(f.path, r)
		link, _ := linkOn(dir, links)
		return inRepo && link == "" && r.Old.Path == mod && (r.Old.Version == "" || r.Old.Version == version)
	})
}

// heldBy returns the path and contents of the go.mod file in previous whose
// module held the directory of the go.mod file at file: that file, or else
// the nearest one in a directory above it. It returns "" if no module held
// the directory.
func heldBy(previous map[string]*modfile.File, file string) (string, *modfile.File) {
	for dir := path.Dir(file); ; dir = path.Dir(dir) {
		p := path.Join(dir, "go.mod")
		if f, ok := previous[p]; ok {
			return p, f
		}
		if dir == "." {
			return "", nil
		}
	}
}

func goLine(f *modfile.File) string {
	if f == nil || f.Go == nil {
		return ""
	}
	return f.Go.Version
}

func toolchainLine(f *modfile.File) string {
	if f == nil || f.Toolchain == nil {
		return ""
	}
	return f.Toolchain.Name
}

// godebugLines returns the settings of f's godebug lines, sorted by key. A
// later line for a key overrides an earlier one, as it does for the go
// command.
func godebugLines(f *modfile.File) string {
	if f == nil {
		return ""
	}
	settings := map[string]string{}
	for _, g := range f.Godebug {
		settings[g.Key] = g.Value
	}
	var lines []string
	for _, k := range slices.Sorted(maps.Keys(settings)) {
		lines = append(lines, k+"="+settings[k])
	}
	return strings.Join(lines, ", ")
}

func main() { checks.Main[Branch](check) }
