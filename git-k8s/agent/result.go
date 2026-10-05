package agent

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net"
	"net/http"
	"strconv"
	"strings"
	"time"
	"unicode"
	"unicode/utf8"

	"github.com/imjasonh/playground/git-k8s/internal/git"
)

// Result is what an agent reports when it finishes. Everything in it comes
// from the agent, so Run checks it before returning it.
type Result struct {
	// Verdict is Pass or Fail.
	Verdict string `json:"verdict"`
	// Summary is one line of at most 200 characters.
	Summary   string `json:"summary"`
	Reasoning string `json:"reasoning"`
	Model     string `json:"model"`
	Usage     Usage  `json:"usage"`
	// CostCents is the run's model token cost before discounts, the Cursor
	// SDK's rawCostCents, when the SDK reports it. It's 0 for usage that's
	// priced by request.
	CostCents *float64 `json:"costCents,omitempty"`
	// ChargedCents is what Cursor charged for the run, with discounts and
	// fees, the Cursor SDK's chargedCents, when the SDK reports it. It's 0
	// for usage that a plan includes.
	ChargedCents *float64 `json:"chargedCents,omitempty"`
	DurationMS   int64    `json:"durationMs"`
	// Files are the files that the agent changed, when its task let it.
	Files []File `json:"files"`
	// MergeTree is set for a job with Checkout.Merge. It's the tree of the
	// merge that git merge-tree wrote in the Pod, which the agent's work
	// tree started with, and which Files change. A controller that commits
	// Files makes the same merge, and checks that its tree is MergeTree, so
	// that the commit holds the files that the agent saw.
	MergeTree string `json:"mergeTree,omitempty"`
	// Error says why the run failed after the agent started. Then Verdict
	// is Fail, Summary, Reasoning, and Files are empty, and Usage and the
	// costs are what the agent used before it failed.
	Error string `json:"error,omitempty"`
}

// Usage is the tokens that a run used, as the Cursor SDK reports them.
type Usage struct {
	InputTokens      int64 `json:"inputTokens"`
	OutputTokens     int64 `json:"outputTokens"`
	CacheReadTokens  int64 `json:"cacheReadTokens"`
	CacheWriteTokens int64 `json:"cacheWriteTokens"`
}

// File is a file that an agent changed. A deleted file has only Path and
// Deleted.
type File struct {
	Path string `json:"path"`
	// Mode is 100644, 100755 for an executable file, or 120000 for a
	// symbolic link, whose Content is its target.
	Mode    string `json:"mode,omitempty"`
	Content []byte `json:"content,omitempty"`
	Deleted bool   `json:"deleted,omitempty"`
}

// Limits on a result. The runner enforces the same ones.
const (
	maxResult    = 16 << 20
	MaxFiles     = 1000
	MaxFileBytes = 8 << 20
	maxSummary   = 200
	maxReasoning = 4000
	maxError     = 3500
	maxModel     = 100
	maxPath      = 4096
)

var errTooBig = fmt.Errorf("it's larger than %d MiB", maxResult>>20)

// client fetches results. It doesn't follow redirects or use a proxy, so a
// Pod can't send the check's request anywhere else.
var client = &http.Client{
	Timeout:       30 * time.Second,
	Transport:     &http.Transport{DisableKeepAlives: true},
	CheckRedirect: func(*http.Request, []*http.Request) error { return http.ErrUseLastResponse },
}

// fetch gets the result that the result container of the Pod with this IP
// and UID serves.
func (r *Runner) fetch(ctx context.Context, ip, uid string) ([]byte, error) {
	return get(ctx, ip, r.resultPort(), uid)
}

// ErrInvalidResult is wrapped by errors from FetchResult for a result that
// fetching again can't fix: one that's too large, or that doesn't match its
// digest.
var ErrInvalidResult = errors.New("invalid result")

// FetchResult gets the file that the runner's serve command serves on port
// in the Pod with this IP and UID, as Run gets an agent's result. It checks
// the file against digest, "sha256:" and the file's SHA-256 in hex, which
// the container that wrote the file reported in its termination message.
// So programs that run other work in Pods can get results without giving
// the Pods credentials.
func FetchResult(ctx context.Context, ip string, port int, uid, digest string) ([]byte, error) {
	if !isDigest(digest) {
		return nil, fmt.Errorf("%w: the Pod reported %.80q, not a SHA-256 digest", ErrInvalidResult, digest)
	}
	body, err := get(ctx, ip, port, uid)
	if errors.Is(err, errTooBig) {
		return nil, fmt.Errorf("%w: %v", ErrInvalidResult, err)
	}
	if err != nil {
		return nil, err
	}
	if sum := sha256.Sum256(body); digest != "sha256:"+hex.EncodeToString(sum[:]) {
		return nil, fmt.Errorf("%w: its digest doesn't match the one that the Pod reported", ErrInvalidResult)
	}
	return body, nil
}

func get(ctx context.Context, ip string, port int, uid string) ([]byte, error) {
	url := "http://" + net.JoinHostPort(ip, strconv.Itoa(port)) + "/result"
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, url, nil)
	if err != nil {
		return nil, err
	}
	req.Header.Set("Authorization", "Bearer "+uid)
	resp, err := client.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("GET %s: %s", url, resp.Status)
	}
	body, err := io.ReadAll(io.LimitReader(resp.Body, maxResult+1))
	if err == nil && len(body) > maxResult {
		err = errTooBig
	}
	return body, err
}

// isDigest reports whether s is a SHA-256 digest, as the runner writes it.
func isDigest(s string) bool {
	h, ok := strings.CutPrefix(s, "sha256:")
	_, err := hex.DecodeString(h)
	return ok && len(h) == 2*sha256.Size && err == nil
}

// parseResult checks a result that a Pod served against the digest that its
// agent container reported, and checks what the agent put in it. edit and
// merge say whether the task edits files and whether the job merges.
func parseResult(body []byte, digest string, edit, merge bool) (*Result, error) {
	sum := sha256.Sum256(body)
	if digest != "sha256:"+hex.EncodeToString(sum[:]) {
		return nil, errors.New("its digest doesn't match the one that the agent container reported")
	}
	var res Result
	if err := json.Unmarshal(body, &res); err != nil {
		return nil, err
	}
	if res.Verdict != Pass && res.Verdict != Fail {
		return nil, fmt.Errorf("its verdict is %.20q, not %s or %s", res.Verdict, Pass, Fail)
	}
	u := res.Usage
	if min(u.InputTokens, u.OutputTokens, u.CacheReadTokens, u.CacheWriteTokens) < 0 || res.CostCents != nil && *res.CostCents < 0 || res.ChargedCents != nil && *res.ChargedCents < 0 {
		return nil, errors.New("it reports negative usage")
	}
	if len(res.Files) > 0 && res.Error != "" {
		return nil, errors.New("it reports an error but also changes files")
	}
	if len(res.Files) > 0 && !edit {
		return nil, errors.New("it changes files, which its task doesn't allow")
	}
	switch {
	// A tree's name has the same form as a commit's.
	case merge && !isCommit(res.MergeTree):
		return nil, fmt.Errorf("its merge tree is %.80q, not the name of a tree", res.MergeTree)
	case !merge && res.MergeTree != "":
		return nil, errors.New("it names a merge tree, but its job merges nothing")
	}
	if err := checkFiles(res.Files); err != nil {
		return nil, err
	}
	res.Summary = clean(res.Summary, maxSummary, true)
	res.Reasoning = clean(res.Reasoning, maxReasoning, false)
	res.Error = clean(res.Error, maxError, false)
	res.Model = clean(res.Model, maxModel, true)
	return &res, nil
}

// clean removes control characters other than newlines and tabs, and
// keeps at most n characters. With oneLine, it also joins the lines.
func clean(s string, n int, oneLine bool) string {
	s = strings.Map(func(r rune) rune {
		switch {
		case oneLine && unicode.IsSpace(r):
			return ' '
		case r == '\n' || r == '\t':
			return r
		case unicode.IsControl(r) || r == utf8.RuneError:
			return -1
		}
		return r
	}, s)
	if oneLine {
		s = strings.Join(strings.Fields(s), " ")
	}
	s = strings.TrimSpace(s)
	if utf8.RuneCountInString(s) > n {
		s = string([]rune(s)[:n-3]) + "..."
	}
	return s
}

// checkFiles checks the files in a result, which the agent controls.
func checkFiles(files []File) error {
	if len(files) > MaxFiles {
		return fmt.Errorf("it changes %d files, more than %d", len(files), MaxFiles)
	}
	seen := make(map[string]bool, len(files))
	size := 0
	for _, f := range files {
		if err := checkPath(f.Path); err != nil {
			return err
		}
		if seen[f.Path] {
			return fmt.Errorf("it changes %q twice", f.Path)
		}
		seen[f.Path] = true
		size += len(f.Content)
		switch {
		case f.Deleted && (f.Mode != "" || len(f.Content) > 0):
			return fmt.Errorf("it deletes %q but also gives it content", f.Path)
		case !f.Deleted && f.Mode != "100644" && f.Mode != "100755" && f.Mode != "120000":
			return fmt.Errorf("it gives %q the mode %.20q, not 100644, 100755, or 120000", f.Path, f.Mode)
		}
	}
	if size > MaxFileBytes {
		return fmt.Errorf("its files hold more than %d MiB", MaxFileBytes>>20)
	}
	return nil
}

// checkPath rejects a path that a tree can't hold, or that's in a .git
// directory.
func checkPath(path string) error {
	ok := path != "" && len(path) <= maxPath && utf8.ValidString(path) && !strings.ContainsFunc(path, unicode.IsControl)
	for part := range strings.SplitSeq(path, "/") {
		ok = ok && part != "" && part != "." && part != ".." && !strings.EqualFold(part, ".git")
	}
	if !ok {
		return fmt.Errorf("it changes a file with an invalid path, %.100q", path)
	}
	return nil
}

// ApplyFiles returns the SHA of a tree that is tree with an agent's changed
// files. It checks the files first, because they come from the agent.
func ApplyFiles(ctx context.Context, repo *git.Repo, tree string, files []File) (string, error) {
	if err := checkFiles(files); err != nil {
		return "", err
	}
	// Deleting first lets a directory replace a file with its name, and a
	// file replace a directory.
	var entries []git.TreeEntry
	for _, f := range files {
		if f.Deleted {
			entries = append(entries, git.TreeEntry{Mode: "0", SHA: strings.Repeat("0", len(tree)), Path: f.Path})
		}
	}
	for _, f := range files {
		if f.Deleted {
			continue
		}
		sha, err := repo.WriteBlob(ctx, f.Content)
		if err != nil {
			return "", err
		}
		entries = append(entries, git.TreeEntry{Mode: f.Mode, Type: "blob", SHA: sha, Path: f.Path})
	}
	return repo.ReplaceFiles(ctx, tree, entries)
}
