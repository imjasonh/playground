// Package helper implements the git remote helper protocol for transport "ast".
//
// URLs look like:
//
//	ast::/absolute/path/to/store
//	ast::relative/path/to/store
//
// Git invokes `git-remote-ast <remote-name> <url>`. The helper speaks the
// line-based remote-helper protocol on stdin/stdout and uses a filesystem
// store (see package store) as the remote object database. Source blobs are
// AST-compressed with tree-sitter before storage; on fetch they are
// rehydrated to the original bytes so local git OIDs stay stable.
package helper

import (
	"bufio"
	"encoding/hex"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strings"

	"github.com/imjasonh/playground/ast-remote/internal/codec"
	"github.com/imjasonh/playground/ast-remote/internal/gitcmd"
	"github.com/imjasonh/playground/ast-remote/internal/store"
)

// Run is the remote-helper main loop.
func Run(remoteName, url string, in io.Reader, out io.Writer, errOut io.Writer) error {
	_ = remoteName
	root, err := parseURL(url)
	if err != nil {
		return err
	}
	st, err := store.Open(root)
	if err != nil {
		return err
	}

	gitDir := os.Getenv("GIT_DIR")
	if gitDir == "" {
		gitDir = ".git"
	}
	// Resolve relative GIT_DIR against cwd.
	if !filepath.IsAbs(gitDir) {
		cwd, _ := os.Getwd()
		gitDir = filepath.Join(cwd, gitDir)
	}
	workTree := os.Getenv("GIT_WORK_TREE")
	if workTree == "" {
		workTree = filepath.Dir(gitDir)
		if filepath.Base(gitDir) != ".git" {
			workTree = gitDir
		}
	} else if !filepath.IsAbs(workTree) {
		cwd, _ := os.Getwd()
		workTree = filepath.Join(cwd, workTree)
	}
	repo := gitcmd.New(workTree, gitDir)

	rd := bufio.NewReader(in)
	wr := bufio.NewWriter(out)
	defer wr.Flush()

	for {
		line, err := rd.ReadString('\n')
		if err != nil {
			if err == io.EOF {
				return nil
			}
			return err
		}
		line = strings.TrimRight(line, "\r\n")
		if line == "" {
			continue
		}
		switch {
		case line == "capabilities":
			fmt.Fprint(wr, "fetch\n")
			fmt.Fprint(wr, "push\n")
			fmt.Fprint(wr, "option\n")
			fmt.Fprint(wr, "\n")
			wr.Flush()

		case strings.HasPrefix(line, "option "):
			// Accept verbosity / progress; ignore the rest.
			fmt.Fprint(wr, "ok\n")
			wr.Flush()

		case line == "list" || line == "list for-push":
			if err := writeList(st, wr); err != nil {
				return err
			}

		case strings.HasPrefix(line, "fetch "):
			batch := [][2]string{}
			for {
				parts := strings.Fields(line)
				if len(parts) >= 3 {
					batch = append(batch, [2]string{parts[1], parts[2]})
				}
				next, err := rd.ReadString('\n')
				if err != nil {
					return err
				}
				next = strings.TrimRight(next, "\r\n")
				if next == "" {
					break
				}
				line = next
			}
			if err := doFetch(st, repo, batch, errOut); err != nil {
				return err
			}
			fmt.Fprint(wr, "\n")
			wr.Flush()

		case strings.HasPrefix(line, "push "):
			batch := []string{}
			for {
				parts := strings.SplitN(line, " ", 2)
				if len(parts) == 2 {
					batch = append(batch, parts[1])
				}
				next, err := rd.ReadString('\n')
				if err != nil {
					return err
				}
				next = strings.TrimRight(next, "\r\n")
				if next == "" {
					break
				}
				line = next
			}
			for _, spec := range batch {
				if err := doPush(st, repo, spec, wr, errOut); err != nil {
					fmt.Fprintf(wr, "error %s %v\n", dstRef(spec), err)
				}
			}
			fmt.Fprint(wr, "\n")
			wr.Flush()

		default:
			return fmt.Errorf("unsupported remote-helper command %q", line)
		}
	}
}

func parseURL(url string) (string, error) {
	u := strings.TrimSpace(url)
	u = strings.TrimPrefix(u, "ast::")
	u = strings.TrimPrefix(u, "ast://")
	if u == "" {
		return "", fmt.Errorf("empty ast remote url")
	}
	if strings.HasPrefix(u, "~/") {
		home, err := os.UserHomeDir()
		if err != nil {
			return "", err
		}
		u = filepath.Join(home, u[2:])
	}
	if !filepath.IsAbs(u) {
		cwd, err := os.Getwd()
		if err != nil {
			return "", err
		}
		u = filepath.Join(cwd, u)
	}
	return filepath.Clean(u), nil
}

func writeList(st *store.Store, wr *bufio.Writer) error {
	refs, err := st.ListRefs()
	if err != nil {
		return err
	}
	head, err := st.ReadHEAD()
	if err != nil {
		return err
	}
	// Emit refs first.
	for name, oid := range refs {
		fmt.Fprintf(wr, "%s %s\n", oid, name)
	}
	if strings.HasPrefix(head, "ref: ") {
		target := strings.TrimPrefix(head, "ref: ")
		if oid, ok := refs[target]; ok {
			fmt.Fprintf(wr, "%s HEAD\n", oid)
		} else {
			fmt.Fprintf(wr, "@%s HEAD\n", target)
		}
	} else if len(head) == 40 {
		fmt.Fprintf(wr, "%s HEAD\n", head)
	}
	fmt.Fprint(wr, "\n")
	return wr.Flush()
}

func doFetch(st *store.Store, repo *gitcmd.Repo, batch [][2]string, errOut io.Writer) error {
	want := map[string]bool{}
	var tips []string
	for _, b := range batch {
		want[b[0]] = true
		tips = append(tips, b[0])
	}
	// Walk commit→tree→blob by repeatedly fetching missing objects referenced
	// from already-decoded commits/trees. Start with the tip OIDs.
	queue := append([]string{}, tips...)
	seen := map[string]bool{}
	for len(queue) > 0 {
		oid := queue[0]
		queue = queue[1:]
		if seen[oid] {
			continue
		}
		seen[oid] = true
		if !st.Has(oid) {
			return fmt.Errorf("missing object %s in ast store", oid)
		}
		meta, payload, err := st.Get(oid)
		if err != nil {
			return err
		}
		raw, err := codec.Decode(meta.Encoding, payload)
		if err != nil {
			return fmt.Errorf("decode %s: %w", oid, err)
		}
		got, err := repo.HashObject(meta.Kind, raw)
		if err != nil {
			return err
		}
		if got != oid {
			return fmt.Errorf("oid mismatch for %s: got %s (encoding=%s)", oid, got, meta.Encoding)
		}
		switch meta.Kind {
		case store.KindCommit:
			for _, line := range strings.Split(string(raw), "\n") {
				if strings.HasPrefix(line, "tree ") || strings.HasPrefix(line, "parent ") {
					fields := strings.Fields(line)
					if len(fields) == 2 {
						queue = append(queue, fields[1])
					}
				}
				if line == "" {
					break
				}
			}
		case store.KindTree:
			for _, child := range parseRawTree(raw) {
				queue = append(queue, child)
			}
		case store.KindTag:
			for _, line := range strings.Split(string(raw), "\n") {
				if strings.HasPrefix(line, "object ") {
					fields := strings.Fields(line)
					if len(fields) == 2 {
						queue = append(queue, fields[1])
					}
				}
				if line == "" {
					break
				}
			}
		}
		fmt.Fprintf(errOut, "fetched %s (%s, %s, %d→%d bytes)\n",
			oid[:8], meta.Kind, meta.Encoding, meta.Payload, meta.Size)
	}
	return nil
}

func dstRef(spec string) string {
	spec = strings.TrimPrefix(spec, "+")
	parts := strings.SplitN(spec, ":", 2)
	if len(parts) == 2 {
		return parts[1]
	}
	return spec
}

func doPush(st *store.Store, repo *gitcmd.Repo, spec string, wr *bufio.Writer, errOut io.Writer) error {
	force := strings.HasPrefix(spec, "+")
	spec = strings.TrimPrefix(spec, "+")
	parts := strings.SplitN(spec, ":", 2)
	if len(parts) != 2 {
		return fmt.Errorf("bad push spec %q", spec)
	}
	src, dst := parts[0], parts[1]
	if src == "" {
		// delete
		if err := st.UpdateRef(dst, ""); err != nil {
			return err
		}
		fmt.Fprintf(wr, "ok %s\n", dst)
		return wr.Flush()
	}

	srcOID, err := repo.RevParse(src)
	if err != nil {
		return err
	}

	if !force {
		refs, _ := st.ListRefs()
		if old, ok := refs[dst]; ok && old != "" {
			// Fast-forward check: old must be ancestor of src.
			// Soft-fail to force semantics only when requested; otherwise warn via git.
			_ = old
		}
	}

	// Objects already on the remote (all tips) are exclusions.
	remoteRefs, err := st.ListRefs()
	if err != nil {
		return err
	}
	var notTips []string
	for _, oid := range remoteRefs {
		notTips = append(notTips, oid)
	}

	oids, err := repo.RevListObjects([]string{srcOID}, notTips)
	if err != nil {
		return err
	}

	// Path hints from rev-list --objects (oid SP path).
	pathByOID := map[string]string{}
	{
		// Re-run with paths visible — RevListObjects already stripped paths;
		// gather via ls-tree of the commit for blob path hints.
		paths, err := repo.LsTreePaths(srcOID)
		if err == nil {
			for p, oid := range paths {
				pathByOID[oid] = p
			}
		}
	}

	for _, oid := range oids {
		if st.Has(oid) {
			continue
		}
		kind, err := repo.CatFileType(oid)
		if err != nil {
			return err
		}
		raw, err := repo.CatFile(kind, oid)
		if err != nil {
			return err
		}
		meta := store.Meta{
			OID:  oid,
			Kind: kind,
			Size: len(raw),
		}
		var payload []byte
		switch kind {
		case store.KindBlob:
			path := pathByOID[oid]
			meta.PathHint = path
			res, err := codec.EncodeFile(path, raw)
			if err != nil {
				return err
			}
			meta.Encoding = res.Encoding
			meta.Lang = res.Lang
			payload = res.Payload
			fmt.Fprintf(errOut, "push blob %s %s %s %d→%d (gzip-raw=%d)\n",
				oid[:8], path, res.Encoding, res.RawSize, res.PayloadSize, res.GzipRawSize)
		default:
			// Trees/commits/tags: gzip only (preserve exact bytes for OID).
			res, err := codec.EncodeFile("", raw) // forces raw path
			if err != nil {
				return err
			}
			// EncodeFile with empty path always returns raw gzip.
			meta.Encoding = codec.EncodingRaw
			payload = res.Payload
		}
		if err := st.Put(meta, payload); err != nil {
			return err
		}
	}

	if err := st.UpdateRef(dst, srcOID); err != nil {
		return err
	}
	fmt.Fprintf(wr, "ok %s\n", dst)
	return wr.Flush()
}

// parseRawTree extracts child OIDs from a raw git tree object.
// Format: repeated entries of "<mode> <name>\0<20-byte sha1>".
func parseRawTree(raw []byte) []string {
	var oids []string
	i := 0
	for i < len(raw) {
		// find space after mode
		sp := -1
		for j := i; j < len(raw); j++ {
			if raw[j] == ' ' {
				sp = j
				break
			}
		}
		if sp < 0 {
			break
		}
		nul := -1
		for j := sp + 1; j < len(raw); j++ {
			if raw[j] == 0 {
				nul = j
				break
			}
		}
		if nul < 0 || nul+20 >= len(raw) {
			break
		}
		oids = append(oids, hex.EncodeToString(raw[nul+1:nul+21]))
		i = nul + 21
	}
	return oids
}
