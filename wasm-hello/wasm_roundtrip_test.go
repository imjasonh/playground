//go:build !wasip1

// Drives the built wasm module the same way the iOS host does — instantiate
// once, then call the exports per request — and checks that a real HTTP
// exchange comes back out. This is the test that would catch the ABI drifting
// away from what the Swift side expects, so it asserts the export names and
// the packed return value explicitly rather than only the response body.
package main_test

import (
	"bufio"
	"bytes"
	"context"
	"encoding/binary"
	"encoding/json"
	"io"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"sync"
	"testing"

	"github.com/tetratelabs/wazero"
	"github.com/tetratelabs/wazero/api"
	"github.com/tetratelabs/wazero/imports/wasi_snapshot_preview1"
)

var (
	buildOnce  sync.Once
	builtWasm  []byte
	buildError error
)

// guestModule builds the wasip1 module once per test binary. Building takes a
// few seconds, which is worth paying to keep a 5 MB binary out of git.
func guestModule(t *testing.T) []byte {
	t.Helper()
	buildOnce.Do(func() {
		directory, err := os.MkdirTemp("", "wasm-hello-build")
		if err != nil {
			buildError = err
			return
		}
		defer os.RemoveAll(directory)

		output := filepath.Join(directory, "hello.wasm")
		command := exec.Command("go", "build", "-buildmode=c-shared", "-o", output, ".")
		command.Env = append(os.Environ(), "GOOS=wasip1", "GOARCH=wasm")
		if combined, err := command.CombinedOutput(); err != nil {
			buildError = &buildFailure{err: err, output: string(combined)}
			return
		}
		builtWasm, buildError = os.ReadFile(output)
	})
	if buildError != nil {
		t.Fatalf("building the wasip1 guest: %v", buildError)
	}
	return builtWasm
}

type buildFailure struct {
	err    error
	output string
}

func (f *buildFailure) Error() string { return f.err.Error() + "\n" + f.output }

// guest is an instantiated module plus the handful of calls the host makes.
type guest struct {
	t      *testing.T
	module api.Module
}

func instantiate(t *testing.T) *guest {
	t.Helper()
	ctx := context.Background()

	runtime := wazero.NewRuntimeWithConfig(ctx, wazero.NewRuntimeConfig())
	t.Cleanup(func() { _ = runtime.Close(ctx) })
	wasi_snapshot_preview1.MustInstantiate(ctx, runtime)

	// WithStartFunctions("_initialize") is the reactor contract: start the Go
	// runtime, then leave the module alive for the host to call into. The
	// default ("_start") would run the program to completion and close it.
	module, err := runtime.InstantiateWithConfig(ctx, guestModule(t),
		wazero.NewModuleConfig().
			WithStartFunctions("_initialize").
			WithStdout(os.Stderr).
			WithStderr(os.Stderr))
	if err != nil {
		t.Fatalf("instantiating the guest: %v", err)
	}
	return &guest{t: t, module: module}
}

func (g *guest) call(name string, arguments ...uint64) uint64 {
	g.t.Helper()
	function := g.module.ExportedFunction(name)
	if function == nil {
		g.t.Fatalf("guest does not export %q", name)
	}
	results, err := function.Call(context.Background(), arguments...)
	if err != nil {
		g.t.Fatalf("calling %s: %v", name, err)
	}
	if len(results) == 0 {
		return 0
	}
	return results[0]
}

// do performs one request exactly as the host does: ask for a buffer, write
// the request bytes into linear memory, call http_handle, then read the
// response back out of the offset and length it packed into one i64.
func (g *guest) do(raw string) *http.Response {
	g.t.Helper()
	request := []byte(raw)

	offset := uint32(g.call("http_alloc", uint64(len(request))))
	if offset == 0 {
		g.t.Fatal("http_alloc returned a null offset")
	}
	if !g.module.Memory().Write(offset, request) {
		g.t.Fatalf("writing %d bytes at %d is out of bounds", len(request), offset)
	}

	packed := g.call("http_handle", uint64(offset), uint64(len(request)))
	if packed == 0 {
		g.t.Fatal("http_handle returned no response")
	}
	responseOffset, responseLength := uint32(packed>>32), uint32(packed)
	raw2, ok := g.module.Memory().Read(responseOffset, responseLength)
	if !ok {
		g.t.Fatalf("reading %d bytes at %d is out of bounds", responseLength, responseOffset)
	}

	response, err := http.ReadResponse(bufio.NewReader(bytes.NewReader(raw2)), nil)
	if err != nil {
		g.t.Fatalf("guest response is not parseable HTTP/1.1: %v\n%q", err, raw2)
	}
	return response
}

func readBody(t *testing.T, response *http.Response) string {
	t.Helper()
	defer response.Body.Close()
	content, err := io.ReadAll(response.Body)
	if err != nil {
		t.Fatalf("reading body: %v", err)
	}
	return string(content)
}

func TestGuestExportsTheHostABI(t *testing.T) {
	guest := instantiate(t)

	if version := guest.call("http_abi_version"); version != 1 {
		t.Errorf("http_abi_version = %d, want 1", version)
	}
	if guest.module.Memory() == nil {
		t.Error("guest exports no memory; the host has nowhere to write requests")
	}
	for _, name := range []string{"http_alloc", "http_handle", "http_abi_version"} {
		if guest.module.ExportedFunction(name) == nil {
			t.Errorf("guest does not export %q", name)
		}
	}
}

func TestGuestServesHello(t *testing.T) {
	response := instantiate(t).do("GET / HTTP/1.1\r\nHost: phone.local\r\n\r\n")
	if response.StatusCode != http.StatusOK {
		t.Fatalf("status = %d, want 200", response.StatusCode)
	}
	body := readBody(t, response)
	if !strings.Contains(body, "Hello from Go") {
		t.Errorf("body does not greet:\n%s", body)
	}
	if !strings.Contains(body, "wasip1/wasm") {
		t.Errorf("body does not report a wasip1 runtime:\n%s", body)
	}
}

// The point of a reactor module is that the instance outlives the request.
// A counter that keeps climbing is the cheapest proof the host is not paying
// to boot the Go runtime again every time.
func TestGuestInstanceOutlivesRequests(t *testing.T) {
	guest := instantiate(t)

	var counts []float64
	for i := 0; i < 3; i++ {
		response := guest.do("GET /info HTTP/1.1\r\nHost: phone.local\r\n\r\n")
		if response.StatusCode != http.StatusOK {
			t.Fatalf("status = %d, want 200", response.StatusCode)
		}
		var info struct {
			GOOS     string  `json:"goos"`
			GOARCH   string  `json:"goarch"`
			Requests float64 `json:"requests"`
		}
		if err := json.Unmarshal([]byte(readBody(t, response)), &info); err != nil {
			t.Fatalf("decoding /info: %v", err)
		}
		if info.GOOS != "wasip1" || info.GOARCH != "wasm" {
			t.Errorf("guest reports %s/%s, want wasip1/wasm", info.GOOS, info.GOARCH)
		}
		counts = append(counts, info.Requests)
	}

	if !(counts[0] < counts[1] && counts[1] < counts[2]) {
		t.Errorf("request counts %v did not increase; the instance is not being reused", counts)
	}
}

func TestGuestReadsRequestBodies(t *testing.T) {
	raw := "POST /echo HTTP/1.1\r\nHost: phone.local\r\nContent-Length: 11\r\n\r\nhello, wasm"
	body := readBody(t, instantiate(t).do(raw))
	if !strings.Contains(body, "hello, wasm") {
		t.Errorf("echo did not return the body:\n%s", body)
	}
	if !strings.Contains(body, "POST /echo HTTP/1.1") {
		t.Errorf("echo did not see the request line:\n%s", body)
	}
}

// A host that points http_handle somewhere it was not given must get a
// response it can send, not a trap and not a read of whatever happens to be at
// that address.
func TestGuestRejectsAnUnallocatedRegion(t *testing.T) {
	guest := instantiate(t)
	request := []byte("GET / HTTP/1.1\r\nHost: h\r\n\r\n")

	offset := uint32(guest.call("http_alloc", uint64(len(request))))
	guest.module.Memory().Write(offset, request)

	packed := guest.call("http_handle", uint64(offset+1), uint64(len(request)))
	if packed == 0 {
		t.Fatal("http_handle returned nothing for a bad region")
	}
	raw, _ := guest.module.Memory().Read(uint32(packed>>32), uint32(packed))
	response, err := http.ReadResponse(bufio.NewReader(bytes.NewReader(raw)), nil)
	if err != nil {
		t.Fatalf("not parseable HTTP/1.1: %v\n%q", err, raw)
	}
	if response.StatusCode != http.StatusBadRequest {
		t.Errorf("status = %d, want 400", response.StatusCode)
	}
}

// Guards the packing convention the Swift host decodes by hand.
func TestPackedResponseIsOffsetThenLength(t *testing.T) {
	guest := instantiate(t)
	request := []byte("GET /healthz HTTP/1.1\r\nHost: h\r\n\r\n")

	offset := uint32(guest.call("http_alloc", uint64(len(request))))
	guest.module.Memory().Write(offset, request)
	packed := guest.call("http_handle", uint64(offset), uint64(len(request)))

	var encoded [8]byte
	binary.BigEndian.PutUint64(encoded[:], packed)
	if high := binary.BigEndian.Uint32(encoded[0:4]); high != uint32(packed>>32) {
		t.Fatalf("packing is not big-endian halves: %x", encoded)
	}
	length := uint32(packed)
	content, ok := guest.module.Memory().Read(uint32(packed>>32), length)
	if !ok || !bytes.HasPrefix(content, []byte("HTTP/1.1 200 OK\r\n")) {
		t.Errorf("low half is not a length into a response: %q", content)
	}
}
