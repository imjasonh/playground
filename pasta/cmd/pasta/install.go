package main

import (
	"bytes"
	"errors"
	"flag"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
)

// preCommitHookMarker is the line that identifies a hook written by
// `pasta install`. Reinstalling and `pasta uninstall` only touch hooks
// that contain it, so changing it strands hooks that older versions
// wrote.
const preCommitHookMarker = "# Installed by `pasta install`. Remove it with `pasta uninstall`."

// executable returns the pasta binary that the hook prefers. It's a
// variable so tests can point the hook at a stub.
var executable = os.Executable

// runInstall writes a git pre-commit hook that runs pasta from the
// current directory, so a commit fails when pasta reports a finding at
// the -fail-on severity or higher. It refuses to replace a hook that
// `pasta install` didn't write unless -force is set.
func runInstall(args []string) int {
	flags := flag.NewFlagSet("pasta install", flag.ExitOnError)
	failOn := flags.String("fail-on", "warning", "block the commit when a finding at this severity or higher is found: none, hint, info, warning, error")
	rulesDir := flags.String("rules", "", "directory of CUE rule files for the hook to load (default: ./"+DefaultRulesDir+")")
	force := flags.Bool("force", false, "replace an existing pre-commit hook that pasta didn't install")
	if err := flags.Parse(args); err != nil {
		return 2
	}
	if flags.NArg() > 0 {
		fmt.Fprintf(os.Stderr, "pasta install: unexpected argument %q\n", flags.Arg(0))
		return 2
	}
	if _, err := parseFailOn(*failOn); err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		return 2
	}
	dir := *rulesDir
	if dir == "" {
		dir = DefaultRulesDir
	}
	if info, err := os.Stat(dir); err != nil || !info.IsDir() {
		switch {
		case *rulesDir == "":
			fmt.Fprintf(os.Stderr, "no ./%s/ directory here; run pasta install from the directory that holds your rules, or pass -rules <dir>\n", DefaultRulesDir)
		case err != nil:
			fmt.Fprintf(os.Stderr, "rules directory: %v\n", err)
		default:
			fmt.Fprintf(os.Stderr, "rules directory %q is not a directory\n", dir)
		}
		return 2
	}
	hookPath, prefix, err := locatePreCommitHook()
	if err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		return 1
	}

	pastaArgs := []string{"-fail-on=" + *failOn}
	if *rulesDir != "" {
		pastaArgs = append(pastaArgs, "-rules="+*rulesDir)
	}
	exe, err := executable()
	if err != nil {
		exe = ""
	}
	script := preCommitHook(prefix, exe, pastaArgs)
	runs := "runs pasta " + shellJoin(pastaArgs)
	if prefix != "" {
		runs += " in " + prefix
	}

	content, ours, err := readHook(hookPath)
	verb := "installed"
	switch {
	case errors.Is(err, os.ErrNotExist):
	case err != nil:
		fmt.Fprintf(os.Stderr, "%v\n", err)
		return 1
	case ours && string(content) == script:
		fmt.Fprintf(os.Stderr, "%s is up to date (%s)\n", hookPath, runs)
		return 0
	case ours:
		verb = "updated"
	case !*force:
		fmt.Fprintf(os.Stderr, "%s already exists and pasta didn't install it; rerun with -force to replace it\n", hookPath)
		return 1
	default:
		verb = "replaced"
	}
	if err := writeHook(hookPath, script); err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		return 1
	}
	fmt.Fprintf(os.Stderr, "%s %s (%s)\n", verb, hookPath, runs)
	return 0
}

// runUninstall removes the pre-commit hook that `pasta install` wrote
// and leaves any other hook in place.
func runUninstall(args []string) int {
	flags := flag.NewFlagSet("pasta uninstall", flag.ExitOnError)
	if err := flags.Parse(args); err != nil {
		return 2
	}
	if flags.NArg() > 0 {
		fmt.Fprintf(os.Stderr, "pasta uninstall: unexpected argument %q\n", flags.Arg(0))
		return 2
	}
	hookPath, _, err := locatePreCommitHook()
	if err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		return 1
	}
	_, ours, err := readHook(hookPath)
	switch {
	case errors.Is(err, os.ErrNotExist):
		fmt.Fprintf(os.Stderr, "no pre-commit hook at %s\n", hookPath)
		return 0
	case err != nil:
		fmt.Fprintf(os.Stderr, "%v\n", err)
		return 1
	case !ours:
		fmt.Fprintf(os.Stderr, "pasta didn't install %s; leaving it in place\n", hookPath)
		return 0
	}
	if err := os.Remove(hookPath); err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		return 1
	}
	fmt.Fprintf(os.Stderr, "removed %s\n", hookPath)
	return 0
}

// locatePreCommitHook asks git where the pre-commit hook for the
// current working tree lives, following core.hooksPath and linked
// worktrees. hookPath is relative to the current directory unless git
// reports it as absolute. prefix is the current directory relative to
// the top of the working tree ("" at the top, otherwise ending in a
// slash). Git runs pre-commit hooks from the top of the working tree,
// so the hook changes into prefix before it runs pasta.
func locatePreCommitHook() (hookPath, prefix string, err error) {
	// --show-toplevel makes git fail outside a working tree (including
	// bare repositories and .git/ itself); its value isn't needed.
	out, err := exec.Command("git", "rev-parse", "--show-toplevel", "--show-prefix", "--git-path", "hooks/pre-commit").Output()
	if err != nil {
		var exitErr *exec.ExitError
		if errors.As(err, &exitErr) && len(exitErr.Stderr) > 0 {
			return "", "", fmt.Errorf("git rev-parse: %s", strings.TrimSpace(string(exitErr.Stderr)))
		}
		return "", "", fmt.Errorf("git rev-parse: %w", err)
	}
	lines := strings.Split(strings.TrimSuffix(string(out), "\n"), "\n")
	if len(lines) != 3 {
		return "", "", fmt.Errorf("git rev-parse: unexpected output %q", out)
	}
	return lines[2], lines[1], nil
}

// preCommitHook returns the hook script. The hook prefers exe, the
// binary that installed it, and falls back to pasta on PATH when exe is
// empty or no longer executable.
func preCommitHook(prefix, exe string, pastaArgs []string) string {
	var b strings.Builder
	b.WriteString("#!/bin/sh\n" + preCommitHookMarker + "\n")
	keyword := "if"
	if exe != "" {
		q := shellQuote(filepath.ToSlash(exe))
		b.WriteString("if [ -x " + q + " ]; then\n\tpasta=" + q + "\n")
		keyword = "elif"
	}
	b.WriteString(keyword + ` command -v pasta >/dev/null 2>&1; then
	pasta=pasta
else
	echo "pasta pre-commit hook: pasta not found; install it, or delete $0 to remove this hook" >&2
	exit 1
fi
`)
	if prefix != "" {
		b.WriteString("cd " + shellQuote("./"+prefix) + " || exit 1\n")
	}
	b.WriteString(`"$pasta" ` + shellJoin(pastaArgs) + `
status=$?
if [ "$status" -ne 0 ]; then
	echo "pasta pre-commit hook: pasta exited with status $status; commit aborted (git commit --no-verify skips this hook)" >&2
fi
exit "$status"
`)
	return b.String()
}

// readHook returns the hook file at path and whether `pasta install`
// wrote it. readHook doesn't follow symlinks, and a symlink or other
// non-regular file never counts as pasta's.
func readHook(path string) (content []byte, ours bool, err error) {
	info, err := os.Lstat(path)
	if err != nil {
		return nil, false, err
	}
	if !info.Mode().IsRegular() {
		return nil, false, nil
	}
	content, err = os.ReadFile(path)
	if err != nil {
		return nil, false, err
	}
	return content, bytes.Contains(content, []byte(preCommitHookMarker)), nil
}

// writeHook replaces path with an executable script. Removing the old
// file first means a symlinked hook is replaced instead of written
// through to its target.
func writeHook(path, script string) error {
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		return err
	}
	if err := os.Remove(path); err != nil && !errors.Is(err, os.ErrNotExist) {
		return err
	}
	return os.WriteFile(path, []byte(script), 0o755)
}

func shellJoin(args []string) string {
	quoted := make([]string, len(args))
	for i, a := range args {
		quoted[i] = shellQuote(a)
	}
	return strings.Join(quoted, " ")
}

// shellQuote quotes s as a single POSIX shell word. A word made only of
// characters that the shell never expands stays bare.
func shellQuote(s string) string {
	unsafe := func(r rune) bool {
		return !(r >= 'a' && r <= 'z' || r >= 'A' && r <= 'Z' || r >= '0' && r <= '9' || strings.ContainsRune("-_./=:,+@%", r))
	}
	if s != "" && strings.IndexFunc(s, unsafe) < 0 {
		return s
	}
	return "'" + strings.ReplaceAll(s, "'", `'\''`) + "'"
}
