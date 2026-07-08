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
	"crypto/sha1"
	"encoding/hex"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"runtime"
	"strings"
	"sync"
	"sync/atomic"

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
	seenTip := map[string]bool{}
	var tips []string
	for _, b := range batch {
		if seenTip[b[0]] {
			continue
		}
		seenTip[b[0]] = true
		tips = append(tips, b[0])
	}

	// Fast path: tip pack written at push time (native git pack of the same
	// objects). Full clone then matches git-daemon: one index-pack, no
	// per-object rehydrate. Protocol objects remain for size / partial fetch.
	// (git clone often sends duplicate fetch lines for HEAD + branch; dedupe.)
	allPacked := len(tips) > 0
	for _, tip := range tips {
		if !st.HasTipPack(tip) {
			allPacked = false
			break
		}
	}
	if allPacked {
		for _, tip := range tips {
			pack, err := st.ReadTipPack(tip)
			if err != nil {
				return err
			}
			fmt.Fprintf(errOut, "fetch tip-pack %s (%d bytes)\n", tip[:8], len(pack))
			if err := repo.IndexPack(pack); err != nil {
				return err
			}
		}
		fmt.Fprintf(errOut, "fetched via tip-pack (%d tip(s))\n", len(tips))
		return nil
	}

	oids, err := st.ListObjectOIDs()
	if err != nil || len(oids) == 0 {
		oids, err = discoverFetchOIDs(st, tips)
		if err != nil {
			return err
		}
	} else {
		for _, tip := range tips {
			if !st.Has(tip) {
				return fmt.Errorf("missing tip %s in ast store", tip)
			}
		}
		fmt.Fprintf(errOut, "fetch inventory: %d objects\n", len(oids))
	}

	workers := runtime.GOMAXPROCS(0)
	if workers < 2 {
		workers = 2
	}
	if workers > 16 {
		workers = 16
	}

	jobs := make(chan string, workers*2)
	errCh := make(chan error, 1)
	var wg sync.WaitGroup
	var done atomic.Int64
	total := int64(len(oids))

	worker := func() {
		defer wg.Done()
		for oid := range jobs {
			meta, payload, err := st.Get(oid)
			if err != nil {
				select {
				case errCh <- err:
				default:
				}
				return
			}
			raw, err := codec.Decode(meta.Encoding, payload)
			if err != nil {
				select {
				case errCh <- fmt.Errorf("decode %s: %w", oid, err):
				default:
				}
				return
			}
			if _, err := repo.WriteObjectExpected(meta.Kind, raw, oid); err != nil {
				select {
				case errCh <- fmt.Errorf("write %s: %w", oid, err):
				default:
				}
				return
			}
			n := done.Add(1)
			if n == total || n%5000 == 0 {
				fmt.Fprintf(errOut, "fetched %d/%d objects\n", n, total)
			}
		}
	}

	wg.Add(workers)
	for i := 0; i < workers; i++ {
		go worker()
	}
	for _, oid := range oids {
		select {
		case err := <-errCh:
			close(jobs)
			wg.Wait()
			return err
		case jobs <- oid:
		}
	}
	close(jobs)
	wg.Wait()
	select {
	case err := <-errCh:
		return err
	default:
	}
	fmt.Fprintf(errOut, "fetched %d objects\n", total)
	return nil
}

func gitOID(kind string, data []byte) string {
	h := sha1.New()
	fmt.Fprintf(h, "%s %d\x00", kind, len(data))
	h.Write(data)
	return hex.EncodeToString(h.Sum(nil))
}

// discoverFetchOIDs walks commit→tree→blob from tips (used when inventory
// listing is unavailable).
func discoverFetchOIDs(st *store.Store, tips []string) ([]string, error) {
	queue := append([]string{}, tips...)
	seen := map[string]bool{}
	var oids []string
	for len(queue) > 0 {
		oid := queue[0]
		queue = queue[1:]
		if seen[oid] {
			continue
		}
		seen[oid] = true
		oids = append(oids, oid)
		if !st.Has(oid) {
			return nil, fmt.Errorf("missing object %s in ast store", oid)
		}
		meta, payload, err := st.Get(oid)
		if err != nil {
			return nil, err
		}
		switch meta.Kind {
		case store.KindBlob:
			continue
		case store.KindCommit, store.KindTree, store.KindTag:
			raw, err := codec.Decode(meta.Encoding, payload)
			if err != nil {
				return nil, fmt.Errorf("decode %s: %w", oid, err)
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
				queue = append(queue, parseRawTree(raw)...)
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
		default:
			return nil, fmt.Errorf("unknown kind %q for %s", meta.Kind, oid)
		}
	}
	return oids, nil
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
	_ = force

	remoteRefs, err := st.ListRefs()
	if err != nil {
		return err
	}
	var notTips []string
	for _, oid := range remoteRefs {
		notTips = append(notTips, oid)
	}

	infos, err := repo.RevListObjectInfos([]string{srcOID}, notTips)
	if err != nil {
		return err
	}

	// Filter to objects not already in the store; keep path hints from rev-list.
	pathByOID := map[string]string{}
	var need []string
	for _, info := range infos {
		if info.Path != "" {
			pathByOID[info.OID] = info.Path
		}
		if !st.Has(info.OID) {
			need = append(need, info.OID)
		}
	}

	fmt.Fprintf(errOut, "pushing %d new objects (%d reachable)\n", len(need), len(infos))
	if len(need) == 0 {
		if err := st.UpdateRef(dst, srcOID); err != nil {
			return err
		}
		fmt.Fprintf(wr, "ok %s\n", dst)
		return wr.Flush()
	}

	// One `git cat-file --batch` instead of 2N subprocesses.
	batch, err := repo.CatFileBatch(need)
	if err != nil {
		return err
	}

	workers := runtime.GOMAXPROCS(0)
	if workers < 2 {
		workers = 2
	}
	if workers > 16 {
		workers = 16
	}

	type job struct {
		obj gitcmd.BatchObject
	}
	jobs := make(chan job, workers*2)
	errCh := make(chan error, 1)
	var wg sync.WaitGroup
	var done atomic.Int64
	total := int64(len(batch))

	worker := func() {
		defer wg.Done()
		for j := range jobs {
			obj := j.obj
			meta := store.Meta{
				OID:  obj.OID,
				Kind: obj.Kind,
				Size: len(obj.Data),
			}
			var payload []byte
			switch obj.Kind {
			case store.KindBlob:
				path := pathByOID[obj.OID]
				meta.PathHint = path
				res, err := codec.EncodeFileOpts(path, obj.Data, codec.EncodeOptions{Fast: true})
				if err != nil {
					select {
					case errCh <- err:
					default:
					}
					return
				}
				meta.Encoding = res.Encoding
				meta.Lang = res.Lang
				payload = res.Payload
			default:
				// Trees/commits/tags: store verbatim. They are already compact,
				// and skipping gzip avoids a useless inflate on every fetch.
				meta.Encoding = codec.EncodingIdentity
				payload = obj.Data
			}
			if err := st.Put(meta, payload); err != nil {
				select {
				case errCh <- err:
				default:
				}
				return
			}
			n := done.Add(1)
			if n == total || n%2000 == 0 {
				fmt.Fprintf(errOut, "pushed %d/%d objects\n", n, total)
			}
		}
	}

	wg.Add(workers)
	for i := 0; i < workers; i++ {
		go worker()
	}
	for _, obj := range batch {
		select {
		case err := <-errCh:
			close(jobs)
			wg.Wait()
			return err
		case jobs <- job{obj: obj}:
		}
	}
	close(jobs)
	wg.Wait()
	select {
	case err := <-errCh:
		return err
	default:
	}

		if err := st.UpdateRef(dst, srcOID); err != nil {
		return err
	}

	// Cache a native tip pack from the source repo so full clones can
	// index-pack without rehydrating every protocol object. Built with
	// git pack-objects (same bytes git-daemon would serve).
	fmt.Fprintf(errOut, "building tip-pack for %s...\n", srcOID[:8])
	pack, err := repo.PackObjects([]string{srcOID})
	if err != nil {
		return fmt.Errorf("tip-pack: %w", err)
	}
	if err := st.WriteTipPack(srcOID, pack); err != nil {
		return err
	}
	fmt.Fprintf(errOut, "tip-pack %d bytes\n", len(pack))

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
