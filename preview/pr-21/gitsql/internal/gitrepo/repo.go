// Package gitrepo opens and caches git repositories for the virtual tables.
//
// A [Manager] resolves a repo "spec" -- a local path, a full clone URL, or an
// "owner/repo" GitHub shorthand -- to an opened go-git repository. Remote repos
// are cloned once (bare) into a local cache directory and reused on subsequent
// runs, so querying the same repo again is fast and works offline. Derived data
// that is expensive to recompute (per-commit file change stats) is memoized in
// memory for the lifetime of the process.
package gitrepo

import (
	"errors"
	"fmt"
	"io"
	"net/url"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"sync"

	"github.com/go-git/go-git/v5"
	"github.com/go-git/go-git/v5/plumbing"
	"github.com/go-git/go-git/v5/plumbing/format/diff"
	"github.com/go-git/go-git/v5/plumbing/object"
)

// Manager resolves repo specs to opened repositories, cloning and caching
// remote repos locally. It is safe for concurrent use.
type Manager struct {
	cacheDir string
	offline  bool
	update   bool
	progress io.Writer

	mu    sync.Mutex
	repos map[string]*Repo
}

// Options configures a [Manager].
type Options struct {
	// CacheDir is where bare clones of remote repos are stored. When empty it
	// defaults to <user cache dir>/gitsql.
	CacheDir string
	// Offline forbids any network access: a remote repo must already be cached.
	Offline bool
	// Update fetches new commits for an already-cached remote repo before use.
	Update bool
	// Progress, when non-nil, receives clone/fetch progress output.
	Progress io.Writer
}

// NewManager returns a Manager using the given options.
func NewManager(opts Options) (*Manager, error) {
	dir := opts.CacheDir
	if dir == "" {
		base, err := os.UserCacheDir()
		if err != nil {
			base = os.TempDir()
		}
		dir = filepath.Join(base, "gitsql")
	}
	return &Manager{
		cacheDir: dir,
		offline:  opts.Offline,
		update:   opts.Update,
		progress: opts.Progress,
		repos:    map[string]*Repo{},
	}, nil
}

// CacheDir reports the directory used to store cached clones.
func (m *Manager) CacheDir() string { return m.cacheDir }

// Resolve returns the opened repository for spec, cloning and caching it first
// if necessary. Repeated calls with the same spec return the same *Repo.
func (m *Manager) Resolve(spec string) (*Repo, error) {
	spec = strings.TrimSpace(spec)
	if spec == "" {
		return nil, errors.New("empty repository spec")
	}
	cloneURL, key, local, err := classifySpec(spec)
	if err != nil {
		return nil, err
	}

	m.mu.Lock()
	defer m.mu.Unlock()
	if r, ok := m.repos[key]; ok {
		return r, nil
	}

	var (
		gr   *git.Repository
		path string
	)
	if local {
		path = key
		gr, err = git.PlainOpenWithOptions(path, &git.PlainOpenOptions{DetectDotGit: true})
		if err != nil {
			return nil, fmt.Errorf("open local repo %q: %w", spec, err)
		}
	} else {
		path = filepath.Join(m.cacheDir, "repos", key)
		gr, err = m.openOrClone(path, cloneURL)
		if err != nil {
			return nil, err
		}
	}

	r := &Repo{
		Spec:     spec,
		CloneURL: cloneURL,
		Path:     path,
		Local:    local,
		repo:     gr,
		stats:    map[plumbing.Hash][]FileChange{},
	}
	m.repos[key] = r
	return r, nil
}

// openOrClone opens a cached bare clone at path, cloning it from cloneURL when
// absent. When the manager is in update mode an existing clone is fetched.
func (m *Manager) openOrClone(path, cloneURL string) (*git.Repository, error) {
	if _, err := os.Stat(filepath.Join(path, "HEAD")); err == nil {
		gr, err := git.PlainOpen(path)
		if err != nil {
			return nil, fmt.Errorf("open cached clone %q: %w", path, err)
		}
		if m.update && !m.offline {
			if m.progress != nil {
				fmt.Fprintf(m.progress, "Updating %s ...\n", cloneURL)
			}
			err := gr.Fetch(&git.FetchOptions{Tags: git.AllTags, Force: true, Progress: m.progress})
			if err != nil && !errors.Is(err, git.NoErrAlreadyUpToDate) {
				return nil, fmt.Errorf("fetch %q: %w", cloneURL, err)
			}
		}
		return gr, nil
	}

	if m.offline {
		return nil, fmt.Errorf("repo %q not in cache and --offline set", cloneURL)
	}
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		return nil, err
	}
	if m.progress != nil {
		fmt.Fprintf(m.progress, "Cloning %s into cache ...\n", cloneURL)
	}
	gr, err := git.PlainClone(path, true, &git.CloneOptions{
		URL:      cloneURL,
		Tags:     git.AllTags,
		Progress: m.progress,
	})
	if err != nil {
		// A failed clone can leave a partial directory behind; remove it so a
		// retry starts clean.
		os.RemoveAll(path)
		return nil, fmt.Errorf("clone %q: %w", cloneURL, err)
	}
	return gr, nil
}

// Repo is a single opened repository plus memoized derived data.
type Repo struct {
	Spec     string // the user-supplied spec
	CloneURL string // resolved clone URL ("" for local repos)
	Path     string // on-disk location (cache dir or local path)
	Local    bool

	repo *git.Repository

	mu    sync.Mutex
	stats map[plumbing.Hash][]FileChange
}

// Git returns the underlying go-git repository.
func (r *Repo) Git() *git.Repository { return r.repo }

// FileChange describes one file touched by a commit, relative to its first
// parent (or the empty tree for a root commit).
type FileChange struct {
	Path      string
	OldPath   string // set for renames; otherwise equal to Path
	Change    string // "add", "delete", "modify", or "rename"
	Additions int
	Deletions int
	Binary    bool
}

// CommitChanges returns the per-file changes a commit introduced relative to
// its first parent. Results are memoized per commit hash.
func (r *Repo) CommitChanges(c *object.Commit) ([]FileChange, error) {
	r.mu.Lock()
	if fc, ok := r.stats[c.Hash]; ok {
		r.mu.Unlock()
		return fc, nil
	}
	r.mu.Unlock()

	fromTree, err := c.Tree()
	if err != nil {
		return nil, err
	}
	// Diff against the first parent, matching `git log` semantics. Root commits
	// diff against the empty tree so every file shows up as an addition.
	parentTree := &object.Tree{}
	if c.NumParents() != 0 {
		p, err := c.Parents().Next()
		if err != nil {
			return nil, err
		}
		parentTree, err = p.Tree()
		if err != nil {
			return nil, err
		}
	}
	patch, err := parentTree.Patch(fromTree)
	if err != nil {
		return nil, err
	}

	var out []FileChange
	for _, fp := range patch.FilePatches() {
		from, to := fp.Files()
		fc := FileChange{Binary: fp.IsBinary()}
		switch {
		case from == nil && to != nil:
			fc.Change, fc.Path, fc.OldPath = "add", to.Path(), to.Path()
		case from != nil && to == nil:
			fc.Change, fc.Path, fc.OldPath = "delete", from.Path(), from.Path()
		case from != nil && to != nil && from.Path() != to.Path():
			fc.Change, fc.Path, fc.OldPath = "rename", to.Path(), from.Path()
		case from != nil && to != nil:
			fc.Change, fc.Path, fc.OldPath = "modify", to.Path(), from.Path()
		default:
			continue
		}
		for _, ch := range fp.Chunks() {
			s := ch.Content()
			if s == "" {
				continue
			}
			n := strings.Count(s, "\n")
			if s[len(s)-1] != '\n' {
				n++
			}
			switch ch.Type() {
			case diff.Add:
				fc.Additions += n
			case diff.Delete:
				fc.Deletions += n
			}
		}
		out = append(out, fc)
	}

	r.mu.Lock()
	r.stats[c.Hash] = out
	r.mu.Unlock()
	return out, nil
}

var ownerRepoRE = regexp.MustCompile(`^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$`)
var scpURLRE = regexp.MustCompile(`^[A-Za-z0-9_.-]+@[A-Za-z0-9_.-]+:.+$`)

// classifySpec turns a user spec into a clone URL plus a stable cache key, and
// reports whether it refers to an on-disk (local) repository.
func classifySpec(spec string) (cloneURL, key string, local bool, err error) {
	if strings.HasPrefix(spec, "~") {
		if home, herr := os.UserHomeDir(); herr == nil {
			spec = filepath.Join(home, strings.TrimPrefix(spec, "~"))
		}
	}

	// An existing path on disk is always treated as a local repo.
	if _, statErr := os.Stat(spec); statErr == nil {
		abs, aerr := filepath.Abs(spec)
		if aerr != nil {
			abs = spec
		}
		return "", abs, true, nil
	}

	switch {
	case hasScheme(spec):
		return spec, remoteKey(spec), false, nil
	case scpURLRE.MatchString(spec):
		return spec, remoteKey(spec), false, nil
	case looksLikePath(spec):
		abs, aerr := filepath.Abs(spec)
		if aerr != nil {
			abs = spec
		}
		return "", abs, true, nil
	case ownerRepoRE.MatchString(spec):
		u := "https://github.com/" + spec
		return u, remoteKey(u), false, nil
	default:
		// Fall back to treating it as a (possibly not-yet-existing) local path.
		abs, aerr := filepath.Abs(spec)
		if aerr != nil {
			abs = spec
		}
		return "", abs, true, nil
	}
}

// looksLikePath reports whether spec is obviously a filesystem path (absolute,
// or explicitly relative with a leading ./ ../ or ~), so it is never mistaken
// for an "owner/repo" GitHub shorthand.
func looksLikePath(spec string) bool {
	switch {
	case filepath.IsAbs(spec):
		return true
	case strings.HasPrefix(spec, "./"), strings.HasPrefix(spec, "../"):
		return true
	case strings.HasPrefix(spec, ".\\"), strings.HasPrefix(spec, "..\\"):
		return true
	case strings.HasPrefix(spec, "~"):
		return true
	}
	return false
}

func hasScheme(spec string) bool {
	for _, s := range []string{"https://", "http://", "git://", "ssh://", "file://"} {
		if strings.HasPrefix(spec, s) {
			return true
		}
	}
	return false
}

var unsafeKeyRE = regexp.MustCompile(`[^A-Za-z0-9._/-]+`)

// remoteKey derives a filesystem-friendly cache key like "github.com/owner/repo"
// from a clone URL (scheme or scp form).
func remoteKey(cloneURL string) string {
	host, path := "", cloneURL
	if u, err := url.Parse(cloneURL); err == nil && u.Host != "" {
		host, path = u.Host, u.Path
	} else if m := strings.SplitN(cloneURL, ":", 2); scpURLRE.MatchString(cloneURL) && len(m) == 2 {
		// git@host:owner/repo.git
		at := strings.SplitN(m[0], "@", 2)
		host = at[len(at)-1]
		path = m[1]
	}
	path = strings.TrimSuffix(strings.Trim(path, "/"), ".git")
	key := host + "/" + path
	key = unsafeKeyRE.ReplaceAllString(key, "_")
	return strings.Trim(key, "/")
}
