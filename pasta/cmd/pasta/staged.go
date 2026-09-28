package main

import (
	"bytes"
	"fmt"
	"path/filepath"
	"strconv"
	"strings"

	"github.com/imjasonh/playground/pasta/internal/runner"
)

// stagedSources returns the files staged for commit under the current
// directory, each with its staged contents rather than its working-tree
// contents. Paths are filtered the way walkSources filters a ./...
// walk: symlinks, submodules, files under a skip directory, and files
// that aren't source files are left out. Files larger than maxFileSize
// (when positive) are returned in oversized instead of specs.
func stagedSources(skip map[string]bool, maxFileSize int64) (specs []runner.FileSpec, oversized []string, err error) {
	// Each entry is ":oldmode newmode oldblob newblob status\0path\0".
	// --relative keeps only paths under the current directory and
	// prints them relative to it. Inside a pre-commit hook, git sets
	// GIT_INDEX_FILE to the index being committed, including the
	// temporary one that `git commit -a` builds.
	out, err := gitOutput(nil, "diff", "--cached", "--raw", "-z", "--no-abbrev", "--no-renames", "--no-color", "--relative", "--diff-filter=AMT")
	if err != nil {
		return nil, nil, err
	}
	var paths, blobIDs []string
	fields := strings.Split(string(out), "\x00")
	for i := 0; i+1 < len(fields); i += 2 {
		meta := strings.Fields(fields[i])
		if len(meta) != 5 {
			return nil, nil, fmt.Errorf("git diff: unexpected output %q", fields[i])
		}
		// Mode 120000 is a symlink and 160000 is a submodule.
		if mode := meta[1]; mode != "100644" && mode != "100755" {
			continue
		}
		p := filepath.FromSlash(fields[i+1])
		if !isSourcePath(p, skip) {
			continue
		}
		paths = append(paths, p)
		blobIDs = append(blobIDs, meta[3])
	}
	blobs, err := readBlobs(blobIDs)
	if err != nil {
		return nil, nil, err
	}
	for i, p := range paths {
		if maxFileSize > 0 && int64(len(blobs[i])) > maxFileSize {
			oversized = append(oversized, p)
			continue
		}
		specs = append(specs, runner.FileSpec{Path: p, Src: blobs[i]})
	}
	return specs, oversized, nil
}

// readBlobs returns the contents of each git blob, in order.
func readBlobs(ids []string) ([][]byte, error) {
	if len(ids) == 0 {
		return nil, nil
	}
	out, err := gitOutput(strings.NewReader(strings.Join(ids, "\n")+"\n"), "cat-file", "--batch")
	if err != nil {
		return nil, err
	}
	blobs := make([][]byte, len(ids))
	for i := range ids {
		// Each object is "<id> blob <size>\n<contents>\n".
		header, rest, _ := bytes.Cut(out, []byte("\n"))
		f := strings.Fields(string(header))
		if len(f) != 3 || f[1] != "blob" {
			return nil, fmt.Errorf("git cat-file: unexpected header %q", header)
		}
		size, err := strconv.Atoi(f[2])
		if err != nil || size < 0 || size >= len(rest) {
			return nil, fmt.Errorf("git cat-file: bad size in %q", header)
		}
		blobs[i] = rest[:size:size]
		out = rest[size+1:]
	}
	return blobs, nil
}

// isSourcePath reports whether a ./... walk would analyze the file at
// the relative path p: no directory in p is in skip, and the file name
// passes isSourceFile.
func isSourcePath(p string, skip map[string]bool) bool {
	dir, name := filepath.Split(p)
	for _, part := range strings.Split(filepath.ToSlash(dir), "/") {
		if skip[part] {
			return false
		}
	}
	return isSourceFile(name)
}
