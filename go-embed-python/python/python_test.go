package python

import (
	"errors"
	"fmt"
	"os"
	"strconv"
	"strings"
	"sync"
	"testing"
)

const testModule = `
import os

import gohost


def double(s):
    return str(int(s) * 2)


def pid(_):
    return str(os.getpid())


def fail(message):
    raise ValueError(message)


def not_a_string(_):
    return 42


def call_go(arg):
    name, _, value = arg.partition(":")
    return gohost.call(name, value)
`

func TestMain(m *testing.M) {
	if err := Start(""); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	if err := LoadModule("testmod", testModule, "<testmod>"); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	code := m.Run()
	if err := Stop(); err != nil {
		fmt.Fprintln(os.Stderr, err)
		code = 1
	}
	os.Exit(code)
}

func lookup(t *testing.T, name string) *Func {
	t.Helper()
	f, err := Lookup("testmod", name)
	if err != nil {
		t.Fatalf("Lookup(%q): %v", name, err)
	}
	return f
}

func TestCall(t *testing.T) {
	got, err := lookup(t, "double").Call("21")
	if err != nil {
		t.Fatal(err)
	}
	if got != "42" {
		t.Errorf("double(21) = %q, want 42", got)
	}
}

func TestPythonRunsInThisProcess(t *testing.T) {
	got, err := lookup(t, "pid").Call("")
	if err != nil {
		t.Fatal(err)
	}
	if want := strconv.Itoa(os.Getpid()); got != want {
		t.Errorf("Python os.getpid() = %s, want the Go process ID %s", got, want)
	}
}

func TestExceptionBecomesError(t *testing.T) {
	_, err := lookup(t, "fail").Call("boom")
	var pyErr *Error
	if !errors.As(err, &pyErr) {
		t.Fatalf("fail() error = %v, want *Error", err)
	}
	if got := pyErr.Error(); got != "ValueError: boom" {
		t.Errorf("Error() = %q, want %q", got, "ValueError: boom")
	}
	if !strings.Contains(pyErr.Traceback, "in fail") {
		t.Errorf("Traceback doesn't mention the raising function:\n%s", pyErr.Traceback)
	}
}

func TestNonStringResultIsTypeError(t *testing.T) {
	_, err := lookup(t, "not_a_string").Call("")
	if err == nil || !strings.HasPrefix(err.Error(), "TypeError") {
		t.Errorf("not_a_string() error = %v, want a TypeError", err)
	}
}

func TestLookupMissingAttribute(t *testing.T) {
	_, err := Lookup("testmod", "no_such_function")
	if err == nil || !strings.HasPrefix(err.Error(), "AttributeError") {
		t.Errorf("Lookup error = %v, want an AttributeError", err)
	}
}

func TestLoadModuleSyntaxError(t *testing.T) {
	err := LoadModule("broken", "def (:\n", "<broken>")
	if err == nil || !strings.HasPrefix(err.Error(), "SyntaxError") {
		t.Errorf("LoadModule error = %v, want a SyntaxError", err)
	}
}

func TestPythonCallsGo(t *testing.T) {
	Expose("reverse", func(s string) (string, error) {
		r := []rune(s)
		for i, j := 0, len(r)-1; i < j; i, j = i+1, j-1 {
			r[i], r[j] = r[j], r[i]
		}
		return string(r), nil
	})
	got, err := lookup(t, "call_go").Call("reverse:gocloud")
	if err != nil {
		t.Fatal(err)
	}
	if got != "duolcog" {
		t.Errorf("gohost.call(reverse, gocloud) = %q, want duolcog", got)
	}
}

func TestGoErrorsRaiseInPython(t *testing.T) {
	Expose("refuse", func(string) (string, error) {
		return "", errors.New("Go says no")
	})
	Expose("explode", func(string) (string, error) {
		panic("unexpected")
	})
	for _, tc := range []struct{ arg, want string }{
		{"refuse:x", "RuntimeError: Go says no"},
		{"explode:x", `RuntimeError: Go function "explode" panicked: unexpected`},
		{"missing:x", `RuntimeError: no Go function registered as "missing"`},
	} {
		_, err := lookup(t, "call_go").Call(tc.arg)
		if err == nil || err.Error() != tc.want {
			t.Errorf("call_go(%q) error = %v, want %q", tc.arg, err, tc.want)
		}
	}
}

func TestConcurrentCalls(t *testing.T) {
	double := lookup(t, "double")
	const workers, calls = 8, 500
	var wg sync.WaitGroup
	var mu sync.Mutex
	var failures []string
	for w := range workers {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for i := range calls {
				n := w*calls + i
				got, err := double.Call(strconv.Itoa(n))
				if err != nil || got != strconv.Itoa(2*n) {
					mu.Lock()
					failures = append(failures, fmt.Sprintf("double(%d) = %q, %v", n, got, err))
					mu.Unlock()
				}
			}
		}()
	}
	wg.Wait()
	if len(failures) > 0 {
		t.Errorf("%d of %d calls failed, first: %s", len(failures), workers*calls, failures[0])
	}
}

func TestStartTwice(t *testing.T) {
	if err := Start(""); err == nil {
		t.Error("second Start succeeded, want an error")
	}
}
