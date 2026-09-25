// Command runpy runs a whole Python program inside this Go process, the way
// Google's gocloud launcher runs gcloud. It passes its own arguments to
// CPython's Py_BytesMain, which behaves like the python3 command:
//
//	runpy -c 'import os; print(os.getpid())'
//	runpy script.py arg1 arg2
package main

/*
#cgo pkg-config: python3-embed
#define PY_SSIZE_T_CLEAN
#include <Python.h>
#include <stdlib.h>
*/
import "C"

import (
	"fmt"
	"os"
	"unsafe"
)

func main() {
	argv := make([]*C.char, len(os.Args))
	for i, arg := range os.Args {
		argv[i] = C.CString(arg)
	}

	fmt.Fprintf(os.Stderr, "[go] pid %d: starting Python in this process\n", os.Getpid())
	// Py_BytesMain parses argv like the python3 command line, runs the
	// program, and finalizes the interpreter, so it runs once per process.
	// When the program calls sys.exit(), Python versions without the fix for
	// CPython issue gh-152132 (3.14.7 has it) end the whole process instead of
	// returning, and the next lines never run.
	code := C.Py_BytesMain(C.int(len(argv)), &argv[0])
	for _, arg := range argv {
		C.free(unsafe.Pointer(arg))
	}
	fmt.Fprintf(os.Stderr, "[go] Python finished with exit code %d; Go is still running\n", code)
	os.Exit(int(code))
}
