# go-embed-python

A running example of a Go program that runs Python inside its own process.
cgo links the program against `libpython`, the library behind the `python3`
command, so Go calls CPython's C API directly. No subprocess starts, and Python
code can call back into Go.

gcloud 574.0.0 and later contain hooks for `gocloud`, an unreleased Go launcher
that runs gcloud's Python code this way. `cmd/runpy` reproduces its approach.

## What's here

| Path | What it shows |
| --- | --- |
| `cmd/runpy` | Runs a whole Python program in-process with `Py_BytesMain`, the way `gocloud` runs gcloud. |
| `cmd/callpy` | Keeps an interpreter running, calls Python functions from Go and from many goroutines, and calls Go from Python. |
| `python/` | The cgo bridge that `callpy` uses: `python.go` is the Go API, and `bridge.c` makes the CPython C API calls. |

## Requirements

- Go, at the version in `go.mod`
- A C compiler, for cgo
- Python 3.12 or later, with its shared library, headers, and `python3-embed`
  pkg-config file

On Debian and Ubuntu, install the `python3-dev` package:

```bash
sudo apt-get install python3-dev
```

The GitHub-hosted Ubuntu runners that CI uses already include it.

## Run it

Build both commands:

```bash
go build -o bin/ ./cmd/...
```

Run a Python program inside the Go process. Python and Go report the same
process ID:

```console
$ bin/runpy -c 'import os, sys; print(os.getpid(), sys.version.split()[0])'
[go] pid 85737: starting Python in this process
85737 3.12.3
[go] Python finished with exit code 0; Go is still running
```

Call Python from Go:

```console
$ bin/callpy
1. Started Python inside this Go process
   /proc/self/maps: /usr/lib/x86_64-linux-gnu/libpython3.12.so.1.0

2. Go calls wordstats.summarize(), whose source is embedded in this binary
   [Go, called from Python] summarize() received 4 words
   count=4 longest="Py_BytesMain"
   Python 3.12.3 got the Go version from a callback: go1.26.0
   Python pid 85749, Go pid 85749, same process: true
   __file__ = <go:embed wordstats.py>
   sys.executable = /usr/bin/python3

3. A Python exception comes back as a Go error
   err = ValueError: bad input from Go

4. Goroutines call Python concurrently; each call holds the GIL
   16000 calls from 8 goroutines in 153ms (9.6 µs per call), 0 wrong results
   Python saw 8 different OS threads

5. For comparison, starting a separate python3 process for each call
   8.7 ms per call

Stopped Python; the Go program keeps running
```

## How it works

### Linking

The cgo preamble in `cmd/runpy/main.go` and `python/python.go` contains
`#cgo pkg-config: python3-embed`. pkg-config supplies the header path and
`-lpython3.X`, so the binary is dynamically linked against `libpython`:

```console
$ ldd bin/runpy | grep python
	libpython3.12.so.1.0 => /lib/x86_64-linux-gnu/libpython3.12.so.1.0
```

When the program starts, the dynamic loader maps `libpython` into the process.
After that, calling Python is a C function call.

### Run a whole program: `runpy`

`cmd/runpy/main.go` converts `os.Args` to C strings and calls `Py_BytesMain`.
That function behaves like the `python3` command: it parses the arguments,
runs the script or `-c` command, finalizes the interpreter, and returns the
exit code. Because it finalizes the interpreter, it runs once per process,
which matches gcloud's model of one command per process.

Two details follow from sharing the process:

- `sys.executable` is the Go binary, because that's the program the process
  runs. gcloud's embedded mode accounts for this when it starts itself again.
- `sys.exit()` returns its exit code to Go only in Python versions that have
  the fix for [CPython issue gh-152132](https://github.com/python/cpython/issues/152132),
  such as 3.14.7. Earlier versions end the whole process from inside
  `Py_BytesMain`, so Go never prints its last line:

  ```console
  $ bin/runpy -c 'import sys; sys.exit(7)'
  [go] pid 85743: starting Python in this process
  $ echo $?
  7
  ```

### Call functions: the `python` package

`callpy` uses the `python` package, which keeps one interpreter running:

1. `Start` initializes CPython with `PyConfig` on a goroutine that stays locked
   to its OS thread, because CPython expects to be finalized on the thread that
   initialized it. `Start` sets `install_signal_handlers = 0` so that the Go
   runtime keeps handling signals, and then releases the global interpreter
   lock (GIL).
1. `LoadModule` compiles source with `Py_CompileString` and imports it with
   `PyImport_ExecCodeModuleEx`. `callpy` passes the contents of
   `//go:embed wordstats.py`, so the Python module lives in the Go binary and
   is never read from disk.
1. `Func.Call` takes the GIL with `PyGILState_Ensure`, calls the function,
   copies the result, and releases the GIL, all inside one C function in
   `bridge.c`. A goroutine can't move to another OS thread during a cgo call,
   so any goroutine can call Python. The calls take turns holding the GIL.
1. `Expose` makes a Go function callable from Python as
   `gohost.call(name, arg)`. `gohost` is a built-in module defined in
   `bridge.c` and registered with `PyImport_AppendInittab` before startup. Its
   C code calls `goCall`, a Go function marked `//export`.
1. A Python exception comes back as a `*python.Error` that holds the formatted
   traceback. If a Go callback returns an error or panics, Python raises
   `RuntimeError`.

Strings cross the boundary as UTF-8 C strings. `callpy` sends and receives JSON
for structured data.

## Build against gcloud's bundled Python

The Linux build of gcloud 586.0.0 bundles Python 3.14.7 as a shared library
with relocatable pkg-config files. To build against it, point pkg-config at
those files and add an rpath so that the binary finds `libpython3.14.so` at run
time:

```bash
PY=/path/to/google-cloud-sdk/platform/bundledpythonunix
PKG_CONFIG_PATH="$PY/lib/pkgconfig" CGO_LDFLAGS="-Wl,-rpath,$PY/lib" go build -o bin/ ./cmd/...
```

When you run the binaries, set `PYTHONHOME` so that Python finds its standard
library. With this version, `sys.exit()` returns to Go:

```console
$ PYTHONHOME=$PY bin/runpy -c 'import sys; print(sys.version.split()[0]); sys.exit(7)'
[go] pid 86367: starting Python in this process
3.14.7
[go] Python finished with exit code 7; Go is still running
```

You can also run gcloud itself the way `gocloud` does. `CLOUDSDK_FROM_GOCLOUD=1`
tells gcloud that it's running embedded:

```console
$ PYTHONHOME=$PY CLOUDSDK_FROM_GOCLOUD=1 bin/runpy /path/to/google-cloud-sdk/lib/gcloud.py version
[go] pid 86373: starting Python in this process
Google Cloud SDK 586.0.0
bq 2.1.38
bundled-python3-unix 3.14.7
core 2026.09.20
gcloud-crc32c 1.0.0
gsutil 5.37
[go] Python finished with exit code 0; Go is still running
```

## Pitfalls

- **The GIL.** Python code never runs in parallel, even from many goroutines. A
  Go callback runs while its Python caller holds the GIL. If the callback waits
  for another goroutine that calls into Python, both block.
- **Signals.** The Go runtime installs its own signal handlers. `runpy`'s
  `Py_BytesMain` installs Python's handlers too. The `python` package turns
  them off.
- **`fork` and `sys.executable`.** A Go process has many threads, so Python's
  `multiprocessing` module must use `spawn`, which starts `sys.executable`. In
  `runpy`, that's the Go binary. In `callpy`, CPython guesses
  `sys.executable` from `PATH`. With gcloud's Python 3.14.7 embedded, it
  reports `/usr/bin/python3`, which is a different Python. If your Python code
  starts subprocesses, set `PyConfig.executable`.
- **Exits.** `PyRun_SimpleString` ends the whole process when the code raises
  `SystemExit`, even in Python 3.14.7. Call functions and fetch exceptions
  yourself, as `bridge.c` does.
- **Restarting.** CPython doesn't support initializing again after it's
  finalized, so `Start` works once per process.

## Test

```bash
go test -race ./...
```

`Py_BytesMain` works once per process, so each `runpy` test runs the test
binary again as `runpy`. `TestSysExitCode` passes on every Python version and
logs whether Go regained control.
