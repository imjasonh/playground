package main

import (
	"bytes"
	"errors"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"testing"
)

const asMainEnv = "RUNPY_TEST_AS_MAIN"

// Py_BytesMain runs once per process, so each test runs this test binary
// again as runpy.
func TestMain(m *testing.M) {
	if os.Getenv(asMainEnv) == "1" {
		main()
		return
	}
	os.Exit(m.Run())
}

type result struct {
	stdout, stderr string
	pid, code      int
}

func runpy(t *testing.T, args ...string) result {
	t.Helper()
	cmd := exec.Command(os.Args[0], args...)
	cmd.Env = append(os.Environ(), asMainEnv+"=1")
	var stdout, stderr bytes.Buffer
	cmd.Stdout, cmd.Stderr = &stdout, &stderr
	var exitErr *exec.ExitError
	if err := cmd.Run(); err != nil && !errors.As(err, &exitErr) {
		t.Fatalf("running runpy %q: %v", args, err)
	}
	return result{stdout.String(), stderr.String(), cmd.Process.Pid, cmd.ProcessState.ExitCode()}
}

func TestPythonRunsInTheGoProcess(t *testing.T) {
	r := runpy(t, "-c", "import os; print(os.getpid())")
	if r.code != 0 {
		t.Fatalf("exit code %d, stderr:\n%s", r.code, r.stderr)
	}
	if got := strings.TrimSpace(r.stdout); got != strconv.Itoa(r.pid) {
		t.Errorf("Python os.getpid() = %s, want the runpy process ID %d", got, r.pid)
	}
	if !strings.Contains(r.stderr, "Go is still running") {
		t.Errorf("Go didn't regain control after Python finished; stderr:\n%s", r.stderr)
	}
}

func TestScriptArguments(t *testing.T) {
	script := filepath.Join(t.TempDir(), "args.py")
	if err := os.WriteFile(script, []byte("import sys\nprint(sys.argv[1:])\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	r := runpy(t, script, "one", "two")
	if r.code != 0 {
		t.Fatalf("exit code %d, stderr:\n%s", r.code, r.stderr)
	}
	if got := strings.TrimSpace(r.stdout); got != "['one', 'two']" {
		t.Errorf("sys.argv[1:] = %s, want ['one', 'two']", got)
	}
}

func TestUncaughtExceptionExitsWithOne(t *testing.T) {
	r := runpy(t, "-c", "raise RuntimeError('boom')")
	if r.code != 1 {
		t.Errorf("exit code %d, want 1", r.code)
	}
	if !strings.Contains(r.stderr, "RuntimeError: boom") {
		t.Errorf("stderr is missing the traceback:\n%s", r.stderr)
	}
}

func TestSysExitCode(t *testing.T) {
	r := runpy(t, "-c", "import sys; sys.exit(7)")
	if r.code != 7 {
		t.Fatalf("exit code %d, want 7; stderr:\n%s", r.code, r.stderr)
	}
	if strings.Contains(r.stderr, "Go is still running") {
		t.Log("Py_BytesMain returned the exit code to Go")
	} else {
		t.Log("this Python exits the process on sys.exit(); see CPython issue gh-152132")
	}
}
