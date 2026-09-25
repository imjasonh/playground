// Command callpy starts a Python interpreter inside this Go process, loads a
// Python module that is embedded in the binary, calls it from Go and from many
// goroutines, and lets the Python code call back into Go.
package main

import (
	"bufio"
	_ "embed"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"os"
	"os/exec"
	"runtime"
	"slices"
	"strconv"
	"strings"
	"sync"
	"time"

	"github.com/imjasonh/playground/go-embed-python/python"
)

//go:embed wordstats.py
var wordstatsSource string

func main() {
	if err := run(os.Stdout); err != nil {
		fmt.Fprintln(os.Stderr, "callpy:", err)
		os.Exit(1)
	}
}

func run(w io.Writer) error {
	python.Expose("go_version", func(string) (string, error) {
		return runtime.Version(), nil
	})
	python.Expose("log", func(msg string) (string, error) {
		fmt.Fprintf(w, "   [Go, called from Python] %s\n", msg)
		return "", nil
	})
	if err := python.Start(""); err != nil {
		return err
	}
	fmt.Fprintln(w, "1. Started Python inside this Go process")
	if lib := mappedLibpython(); lib != "" {
		fmt.Fprintf(w, "   /proc/self/maps: %s\n", lib)
	}

	if err := python.LoadModule("wordstats", wordstatsSource, "<go:embed wordstats.py>"); err != nil {
		return err
	}
	funcs := map[string]*python.Func{}
	for _, name := range []string{"summarize", "square", "thread_id", "fail"} {
		f, err := python.Lookup("wordstats", name)
		if err != nil {
			return err
		}
		funcs[name] = f
	}

	fmt.Fprintln(w, "\n2. Go calls wordstats.summarize(), whose source is embedded in this binary")
	payload, err := json.Marshal(map[string][]string{"words": {"gcloud", "gocloud", "cgo", "Py_BytesMain"}})
	if err != nil {
		return err
	}
	out, err := funcs["summarize"].Call(string(payload))
	if err != nil {
		return err
	}
	var stats struct {
		Count         int    `json:"count"`
		Longest       string `json:"longest"`
		PythonVersion string `json:"python_version"`
		GoVersion     string `json:"go_version"`
		PID           int    `json:"pid"`
		ModuleFile    string `json:"module_file"`
		Executable    string `json:"executable"`
	}
	if err := json.Unmarshal([]byte(out), &stats); err != nil {
		return err
	}
	fmt.Fprintf(w, "   count=%d longest=%q\n", stats.Count, stats.Longest)
	fmt.Fprintf(w, "   Python %s got the Go version from a callback: %s\n", stats.PythonVersion, stats.GoVersion)
	fmt.Fprintf(w, "   Python pid %d, Go pid %d, same process: %t\n", stats.PID, os.Getpid(), stats.PID == os.Getpid())
	fmt.Fprintf(w, "   __file__ = %s\n", stats.ModuleFile)
	fmt.Fprintf(w, "   sys.executable = %s\n", stats.Executable)

	fmt.Fprintln(w, "\n3. A Python exception comes back as a Go error")
	_, err = funcs["fail"].Call("bad input from Go")
	var pyErr *python.Error
	if !errors.As(err, &pyErr) {
		return fmt.Errorf("fail() returned %v, want a *python.Error", err)
	}
	fmt.Fprintf(w, "   err = %v\n", err)

	fmt.Fprintln(w, "\n4. Goroutines call Python concurrently; each call holds the GIL")
	const workers, perWorker = 8, 2000
	var wg sync.WaitGroup
	var mu sync.Mutex
	wrong := 0
	threads := map[string]bool{}
	start := time.Now()
	for g := range workers {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for i := range perWorker {
				n := g*perWorker + i
				got, err := funcs["square"].Call(strconv.Itoa(n))
				if err != nil || got != strconv.Itoa(n*n) {
					mu.Lock()
					wrong++
					mu.Unlock()
				}
			}
			tid, err := funcs["thread_id"].Call("")
			mu.Lock()
			if err == nil {
				threads[tid] = true
			}
			mu.Unlock()
		}()
	}
	wg.Wait()
	elapsed := time.Since(start)
	fmt.Fprintf(w, "   %d calls from %d goroutines in %v (%.1f µs per call), %d wrong results\n",
		workers*perWorker, workers, elapsed.Round(time.Millisecond),
		float64(elapsed.Microseconds())/(workers*perWorker), wrong)
	fmt.Fprintf(w, "   Python saw %d different OS threads\n", len(threads))

	fmt.Fprintln(w, "\n5. For comparison, starting a separate python3 process for each call")
	if perCall, err := timePythonProcess(10); err != nil {
		fmt.Fprintf(w, "   skipped: %v\n", err)
	} else {
		fmt.Fprintf(w, "   %.1f ms per call\n", float64(perCall.Microseconds())/1000)
	}

	if err := python.Stop(); err != nil {
		return err
	}
	fmt.Fprintln(w, "\nStopped Python; the Go program keeps running")
	return nil
}

// timePythonProcess runs python3 from PATH runs times and returns the average
// time per run.
func timePythonProcess(runs int) (time.Duration, error) {
	py, err := exec.LookPath("python3")
	if err != nil {
		return 0, err
	}
	// PYTHONHOME is meant for the embedded interpreter, which can be a
	// different Python than the python3 on PATH.
	env := slices.DeleteFunc(os.Environ(), func(kv string) bool {
		return strings.HasPrefix(kv, "PYTHONHOME=")
	})
	start := time.Now()
	for range runs {
		cmd := exec.Command(py, "-c", "pass")
		cmd.Env = env
		if err := cmd.Run(); err != nil {
			return 0, fmt.Errorf("%s: %w", py, err)
		}
	}
	return time.Since(start) / time.Duration(runs), nil
}

// mappedLibpython returns the path of the libpython shared library mapped
// into this process, or "" if /proc/self/maps isn't available.
func mappedLibpython() string {
	f, err := os.Open("/proc/self/maps")
	if err != nil {
		return ""
	}
	defer f.Close()
	sc := bufio.NewScanner(f)
	for sc.Scan() {
		line := sc.Text()
		if i := strings.Index(line, "/"); i >= 0 && strings.Contains(line, "libpython") {
			return line[i:]
		}
	}
	return ""
}
