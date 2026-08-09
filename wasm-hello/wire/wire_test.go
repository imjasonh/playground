package wire_test

import (
	"bufio"
	"bytes"
	"fmt"
	"io"
	"net/http"
	"strings"
	"testing"

	"github.com/imjasonh/playground/wasm-hello/wire"
)

// serve runs raw request bytes through wire.Serve and parses what comes back,
// which is exactly the round trip the host performs across linear memory.
func serve(t *testing.T, handler http.Handler, raw string) *http.Response {
	t.Helper()
	out := wire.Serve(handler, []byte(raw))
	response, err := http.ReadResponse(bufio.NewReader(bytes.NewReader(out)), nil)
	if err != nil {
		t.Fatalf("response is not parseable HTTP/1.1: %v\n%q", err, out)
	}
	return response
}

func body(t *testing.T, response *http.Response) string {
	t.Helper()
	defer response.Body.Close()
	content, err := io.ReadAll(response.Body)
	if err != nil {
		t.Fatalf("reading body: %v", err)
	}
	return string(content)
}

func TestServeRoundTrip(t *testing.T) {
	handler := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("X-Method", r.Method)
		w.Header().Set("Content-Type", "text/plain")
		fmt.Fprintf(w, "path=%s host=%s", r.URL.Path, r.Host)
	})

	response := serve(t, handler, "GET /hello?x=1 HTTP/1.1\r\nHost: example.test\r\n\r\n")
	if response.StatusCode != http.StatusOK {
		t.Fatalf("status = %d, want 200", response.StatusCode)
	}
	if got := response.Header.Get("X-Method"); got != "GET" {
		t.Errorf("X-Method = %q, want GET", got)
	}
	if got := body(t, response); got != "path=/hello host=example.test" {
		t.Errorf("body = %q", got)
	}
}

// The host frames the response by length, so a missing or wrong Content-Length
// would truncate or hang it.
func TestServeSetsContentLength(t *testing.T) {
	handler := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		fmt.Fprint(w, "0123456789")
	})

	response := serve(t, handler, "GET / HTTP/1.1\r\nHost: h\r\n\r\n")
	if response.ContentLength != 10 {
		t.Errorf("ContentLength = %d, want 10", response.ContentLength)
	}
	if got := response.Header.Get("Transfer-Encoding"); got != "" {
		t.Errorf("Transfer-Encoding = %q, want none", got)
	}
}

func TestServeRequestBody(t *testing.T) {
	handler := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		content, err := io.ReadAll(r.Body)
		if err != nil {
			t.Errorf("handler could not read body: %v", err)
		}
		fmt.Fprintf(w, "got %d bytes: %s", len(content), content)
	})

	raw := "POST /echo HTTP/1.1\r\nHost: h\r\nContent-Length: 5\r\n\r\nhello"
	if got := body(t, serve(t, handler, raw)); got != "got 5 bytes: hello" {
		t.Errorf("body = %q", got)
	}
}

func TestServeStatusAndHeaders(t *testing.T) {
	handler := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.Header().Add("X-Repeated", "one")
		w.Header().Add("X-Repeated", "two")
		w.WriteHeader(http.StatusTeapot)
	})

	response := serve(t, handler, "GET / HTTP/1.1\r\nHost: h\r\n\r\n")
	if response.StatusCode != http.StatusTeapot {
		t.Fatalf("status = %d, want 418", response.StatusCode)
	}
	if got := response.Header.Values("X-Repeated"); len(got) != 2 {
		t.Errorf("X-Repeated = %v, want two values", got)
	}
}

// Garbage in has to produce a valid response, not a panic: the host has a
// socket open and needs something to write to it.
func TestServeRejectsGarbage(t *testing.T) {
	never := http.HandlerFunc(func(http.ResponseWriter, *http.Request) {
		t.Error("handler ran for an unparseable request")
	})

	response := serve(t, never, "this is not HTTP\r\n\r\n")
	if response.StatusCode != http.StatusBadRequest {
		t.Errorf("status = %d, want 400", response.StatusCode)
	}
}

func TestServeRejectsOversizedRequest(t *testing.T) {
	never := http.HandlerFunc(func(http.ResponseWriter, *http.Request) {
		t.Error("handler ran for an oversized request")
	})

	raw := "GET / HTTP/1.1\r\nHost: h\r\nX-Big: " + strings.Repeat("a", wire.MaxRequestSize) + "\r\n\r\n"
	response := serve(t, never, raw)
	if response.StatusCode != http.StatusRequestEntityTooLarge {
		t.Errorf("status = %d, want 413", response.StatusCode)
	}
}
