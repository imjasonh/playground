package gocache

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"io/fs"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"strconv"
	"strings"
	"text/scanner"
	"unicode"
)

// Build compiles the packages that go test ./... needs in the current
// directory's module and that no branch can change: those in GOROOT, which
// the toolchain fixes, and those in the module cache, which go.sum pins. It
// compiles them with go list -export, which neither links nor runs
// anything, and with GOCACHEPROG set to cacheprog, a Prog with Remote and
// Share set, so their outputs come from the build cache or go to it. It
// returns the import paths that it compiled, and how many packages go test
// needs.
//
// Build leaves out the module's own packages, including vendored ones and
// modules that a replace directive points at a directory, and the packages
// that import them, so go test compiles them without sharing their outputs.
// Action IDs don't cover every file that a build step reads. An assembly
// file can include a file from anywhere, so two branches can compile
// different outputs for one action ID.
func Build(ctx context.Context, cacheprog string, stderr io.Writer) (shared []string, total int, err error) {
	out, err := goCommand(ctx, nil, stderr, "env", "-json", "GOROOT", "GOMODCACHE")
	if err != nil {
		return nil, 0, err
	}
	var env struct{ GOROOT, GOMODCACHE string }
	if err := json.Unmarshal(out, &env); err != nil {
		return nil, 0, fmt.Errorf("go env: %w", err)
	}
	out, err = goCommand(ctx, nil, stderr, "list", "-e", "-deps", "-test", "-json=ImportPath,Dir,ForTest,SFiles,Deps", "./...")
	if err != nil {
		return nil, 0, err
	}
	var pkgs []listedPackage
	for dec := json.NewDecoder(bytes.NewReader(out)); ; {
		var p listedPackage
		if err := dec.Decode(&p); errors.Is(err, io.EOF) {
			break
		} else if err != nil {
			return nil, 0, fmt.Errorf("go list: %w", err)
		}
		pkgs = append(pkgs, p)
	}
	shared = shareable(pkgs, env.GOROOT, env.GOMODCACHE)
	if len(shared) > 0 {
		args := append([]string{"list", "-e", "-export", `-f={{""}}`}, shared...)
		if _, err := goCommand(ctx, []string{"GOCACHEPROG=" + cacheprog}, stderr, args...); err != nil {
			return nil, len(pkgs), err
		}
	}
	return shared, len(pkgs), nil
}

func goCommand(ctx context.Context, env []string, stderr io.Writer, args ...string) ([]byte, error) {
	cmd := exec.CommandContext(ctx, "go", args...)
	cmd.Env = append(os.Environ(), env...)
	cmd.Stderr = stderr
	out, err := cmd.Output()
	if err != nil {
		return nil, fmt.Errorf("go %s: %w", args[0], err)
	}
	return out, nil
}

// listedPackage holds the fields of go list -json that Build uses.
type listedPackage struct {
	ImportPath string
	Dir        string
	ForTest    string
	SFiles     []string
	Deps       []string
}

// shareable returns the import paths of the packages whose outputs no
// branch can change. Such a package is in goroot or modcache and isn't a
// test variant, its assembly includes only files as fixed as the package,
// and it imports only such packages.
func shareable(pkgs []listedPackage, goroot, modcache string) []string {
	fixed := map[string]bool{}
	for _, p := range pkgs {
		fixed[p.ImportPath] = p.ForTest == "" && fixedDir(p.Dir, goroot, modcache) && includesStayIn(p.Dir, p.SFiles)
	}
	var paths []string
	for _, p := range pkgs {
		if fixed[p.ImportPath] && !slices.ContainsFunc(p.Deps, func(d string) bool { return !fixed[d] }) {
			paths = append(paths, p.ImportPath)
		}
	}
	return paths
}

// fixedDir reports whether dir is in goroot, or in modcache, where the go
// command extracts each module after checking it against go.sum.
// modcache/cache holds downloads, not packages.
func fixedDir(dir, goroot, modcache string) bool {
	if !filepath.IsAbs(dir) {
		return false
	}
	dir = filepath.Clean(dir)
	return within(dir, goroot) || (within(dir, modcache) && !within(dir, filepath.Join(modcache, "cache")))
}

// within reports whether path, which is clean, is root or inside it.
func within(path, root string) bool {
	if !filepath.IsAbs(root) {
		return false
	}
	root = strings.TrimSuffix(filepath.Clean(root), string(filepath.Separator))
	return path == root || strings.HasPrefix(path, root+string(filepath.Separator))
}

// includesStayIn reports whether the assembly files in dir include only
// files as fixed as dir. The assembler looks for an included file in its
// working directory, which is dir, and then in the go command's work
// directory and in GOROOT/pkg/include. A name that isn't local, such as
// /src/repo/x.h or ../x.h, can reach other files.
func includesStayIn(dir string, sfiles []string) bool {
	seen := map[string]bool{}
	var stays func(name string) bool
	stays = func(name string) bool {
		if seen[name] {
			return true
		}
		seen[name] = true
		src, err := os.ReadFile(filepath.Join(dir, name))
		if err != nil {
			return false
		}
		names, ok := asmStrings(src)
		if !ok {
			return false
		}
		for _, n := range names {
			if n == "" || strings.ContainsRune(n, 0) {
				// The assembler can't open a file by either name.
				continue
			}
			if !filepath.IsLocal(n) {
				return false
			}
			fi, err := os.Lstat(filepath.Join(dir, n))
			switch {
			case errors.Is(err, fs.ErrNotExist):
			case err != nil || !fi.Mode().IsRegular() || !stays(n):
				return false
			}
		}
		return true
	}
	return !slices.ContainsFunc(sfiles, func(f string) bool { return !stays(f) })
}

// asmStrings returns the string literals in an assembly file, which it
// tokenizes as cmd/asm does. #include takes its file name from a string
// literal, which no macro can build, so every name that a file can include
// is among them.
func asmStrings(src []byte) ([]string, bool) {
	var s scanner.Scanner
	s.Init(bytes.NewReader(src))
	s.Whitespace = 1<<'\t' | 1<<'\r' | 1<<' '
	s.Mode = scanner.ScanChars | scanner.ScanFloats | scanner.ScanIdents | scanner.ScanInts | scanner.ScanStrings | scanner.ScanComments
	s.IsIdentRune = func(ch rune, i int) bool {
		return unicode.IsLetter(ch) || ch == '_' || ch == '\u00B7' || ch == '\u2215' || (i > 0 && unicode.IsDigit(ch))
	}
	s.Error = func(*scanner.Scanner, string) {}
	var strs []string
	for tok := s.Scan(); tok != scanner.EOF; tok = s.Scan() {
		if tok != scanner.String {
			continue
		}
		str, err := strconv.Unquote(s.TokenText())
		if err != nil {
			return nil, false
		}
		strs = append(strs, str)
	}
	return strs, s.ErrorCount == 0
}
