// Package python runs a CPython interpreter inside the current Go process.
//
// cgo links the program against libpython, the library behind the python3
// command, so Go and Python share one process, one address space, and one set
// of OS threads. Python code calls back into Go through the built-in gohost
// module; see Expose.
//
// Call Start once. After that, LoadModule, Lookup, and Func.Call are safe to
// use from any goroutine: each call holds Python's global interpreter lock
// (GIL) for its duration, so Python code never runs in parallel.
package python

/*
#cgo pkg-config: python3-embed
#include <stdlib.h>
#include "bridge.h"
*/
import "C"

import (
	"errors"
	"fmt"
	"runtime"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"unsafe"
)

// ErrNotRunning reports a call made before Start or after Stop.
var ErrNotRunning = errors.New("python: interpreter is not running")

var (
	lifecycle sync.Mutex
	started   bool // CPython can't be initialized twice in one process.
	running   atomic.Bool
	stopReq   chan chan C.int
)

// Start initializes the interpreter. home is the Python installation prefix:
// the directory whose lib/python3.X subdirectory holds the standard library.
// If home is empty, Python uses PYTHONHOME or the prefix that libpython was
// built with. Start succeeds at most once per process.
func Start(home string) error {
	lifecycle.Lock()
	defer lifecycle.Unlock()
	if started {
		return errors.New("python: Start can only be called once per process")
	}
	started = true

	ready := make(chan error)
	stop := make(chan chan C.int)
	go func() {
		// CPython must be initialized and finalized on the same OS thread, so
		// this goroutine keeps its thread for the life of the interpreter.
		runtime.LockOSThread()
		chome := C.CString(home)
		var cerr *C.char
		failed := C.bridge_start(chome, &cerr) != 0
		C.free(unsafe.Pointer(chome))
		if failed {
			ready <- errors.New("python: " + takeString(cerr))
			return
		}
		ready <- nil
		done := <-stop
		done <- C.bridge_stop()
	}()
	if err := <-ready; err != nil {
		return err
	}
	stopReq = stop
	running.Store(true)
	return nil
}

// Stop finalizes the interpreter. No other call may be in progress. Calls
// made after Stop return ErrNotRunning.
func Stop() error {
	lifecycle.Lock()
	defer lifecycle.Unlock()
	if !running.Load() {
		return ErrNotRunning
	}
	running.Store(false)
	done := make(chan C.int)
	stopReq <- done
	if <-done != 0 {
		return errors.New("python: finalization failed")
	}
	return nil
}

// LoadModule compiles source and imports the result as the module name, as
// if it had been read from filename. Nothing is read from disk, so the source
// can come from a go:embed string.
func LoadModule(name, source, filename string) error {
	if !running.Load() {
		return ErrNotRunning
	}
	cname, csource, cfilename := C.CString(name), C.CString(source), C.CString(filename)
	defer C.free(unsafe.Pointer(cname))
	defer C.free(unsafe.Pointer(csource))
	defer C.free(unsafe.Pointer(cfilename))
	var cerr *C.char
	if C.bridge_load_module(cname, csource, cfilename, &cerr) != 0 {
		return pythonError(cerr)
	}
	return nil
}

// Func is a Python callable that takes one str and returns a str.
type Func struct {
	obj unsafe.Pointer // A PyObject* that this Func holds a reference to.
}

// Lookup returns the attribute attr of the importable module, which must be
// callable with one str argument.
func Lookup(module, attr string) (*Func, error) {
	if !running.Load() {
		return nil, ErrNotRunning
	}
	cmodule, cattr := C.CString(module), C.CString(attr)
	defer C.free(unsafe.Pointer(cmodule))
	defer C.free(unsafe.Pointer(cattr))
	var cerr *C.char
	obj := C.bridge_lookup(cmodule, cattr, &cerr)
	if obj == nil {
		return nil, pythonError(cerr)
	}
	return &Func{obj: obj}, nil
}

// Call calls f with arg and returns its result. If Python raises, the error
// is an *Error. A result that isn't a str is reported as a TypeError. Strings
// cross into C as NUL-terminated UTF-8, so they can't contain NUL bytes.
func (f *Func) Call(arg string) (string, error) {
	if !running.Load() {
		return "", ErrNotRunning
	}
	carg := C.CString(arg)
	defer C.free(unsafe.Pointer(carg))
	var cerr *C.char
	out := C.bridge_call(f.obj, carg, &cerr)
	if out == nil {
		return "", pythonError(cerr)
	}
	return takeString(out), nil
}

// Error is a Python exception that escaped from a call.
type Error struct {
	// Traceback is the exception as Python's traceback module formats it.
	Traceback string
}

// Error returns the last line of the traceback, such as "ValueError: boom".
func (e *Error) Error() string {
	lines := strings.Split(strings.TrimSpace(e.Traceback), "\n")
	return lines[len(lines)-1]
}

func pythonError(cerr *C.char) error {
	if cerr == nil {
		return errors.New("python: out of memory")
	}
	return &Error{Traceback: takeString(cerr)}
}

// takeString copies a malloc'd C string into Go memory and frees it.
func takeString(s *C.char) string {
	if s == nil {
		return "out of memory"
	}
	defer C.free(unsafe.Pointer(s))
	return C.GoString(s)
}

var (
	callbacksMu sync.RWMutex
	callbacks   = map[string]func(string) (string, error){}
)

// Expose makes fn callable from Python code as gohost.call(name, arg). If fn
// returns an error or panics, the Python call raises RuntimeError. fn runs
// while its Python caller holds the GIL, so it must not wait for another
// goroutine that calls into Python.
func Expose(name string, fn func(arg string) (string, error)) {
	callbacksMu.Lock()
	defer callbacksMu.Unlock()
	callbacks[name] = fn
}

// goCall implements gohost.call for bridge.c. It returns a malloc'd result,
// or stores a malloc'd message in *errOut and returns NULL. A panic can't
// unwind through the C frames of the Python caller, so it becomes an error.
//
//export goCall
func goCall(name, arg *C.char, errOut **C.char) (result *C.char) {
	key := C.GoString(name)
	defer func() {
		if r := recover(); r != nil {
			*errOut = C.CString(fmt.Sprintf("Go function %q panicked: %v", key, r))
			result = nil
		}
	}()
	callbacksMu.RLock()
	fn, ok := callbacks[key]
	callbacksMu.RUnlock()
	if !ok {
		*errOut = C.CString("no Go function registered as " + strconv.Quote(key))
		return nil
	}
	out, err := fn(C.GoString(arg))
	if err != nil {
		*errOut = C.CString(err.Error())
		return nil
	}
	return C.CString(out)
}
