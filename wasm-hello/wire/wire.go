// Package wire runs one HTTP exchange entirely in memory: raw HTTP/1.1 request
// bytes in, raw HTTP/1.1 response bytes out.
//
// That byte-for-byte framing is the whole ABI between the iOS host and this
// guest. The host is already holding the request bytes it read off a socket
// and is about to write response bytes back to it, so handing those across
// unchanged means there is no second wire format to invent, version, or keep
// in sync — and any language with an HTTP/1.1 parser can implement the guest
// side of it. Ordinary net/http does both directions here.
package wire

import (
	"bufio"
	"bytes"
	"fmt"
	"io"
	"net/http"
	"sort"
	"strconv"
)

// MaxRequestSize bounds what the guest will parse. A wasm module cannot grow
// past its memory limit and has nowhere to spill, so an oversized request has
// to be refused rather than absorbed.
const MaxRequestSize = 8 << 20

// BadRequest is a ready-made 400 for a host that could not even hand over a
// request. The host has a socket open and needs bytes to write to it, so every
// failure path has to produce a response.
func BadRequest(detail string) []byte {
	return errorResponse(http.StatusBadRequest, detail)
}

// Serve parses one request, runs it through h, and serializes the response.
// It never returns an error: a request this function cannot understand becomes
// a 4xx response, because the host's only sensible move would be to send one
// anyway.
func Serve(h http.Handler, raw []byte) []byte {
	if len(raw) > MaxRequestSize {
		return errorResponse(http.StatusRequestEntityTooLarge,
			fmt.Sprintf("request is %d bytes, limit is %d", len(raw), MaxRequestSize))
	}

	request, err := http.ReadRequest(bufio.NewReader(bytes.NewReader(raw)))
	if err != nil {
		return errorResponse(http.StatusBadRequest, "could not parse request: "+err.Error())
	}
	// ReadRequest fills RequestURI (it is parsing a server-side request) but
	// leaves RemoteAddr empty, and handlers reasonably expect something there.
	if request.RemoteAddr == "" {
		request.RemoteAddr = "wasm-host:0"
	}
	defer func() {
		if request.Body != nil {
			_ = request.Body.Close()
		}
	}()

	recorder := &recorder{header: http.Header{}, status: http.StatusOK}
	h.ServeHTTP(recorder, request)
	return recorder.serialize()
}

// recorder is a minimal http.ResponseWriter. net/http/httptest has one, but it
// drags crypto/tls and flag into the module for the sake of thirty lines, and
// every megabyte here is a megabyte an interpreter on a phone has to parse.
type recorder struct {
	header      http.Header
	status      int
	body        bytes.Buffer
	wroteHeader bool
}

func (r *recorder) Header() http.Header { return r.header }

func (r *recorder) WriteHeader(status int) {
	if r.wroteHeader {
		return
	}
	r.status = status
	r.wroteHeader = true
}

func (r *recorder) Write(p []byte) (int, error) {
	r.WriteHeader(r.status)
	return r.body.Write(p)
}

// Flush exists so handlers that stream do not panic on the type assertion.
// Buffering everything is the only option here: the response leaves as one
// blob, so there is nothing to flush to.
func (r *recorder) Flush() {}

func (r *recorder) serialize() []byte {
	var out bytes.Buffer
	fmt.Fprintf(&out, "HTTP/1.1 %d %s\r\n", r.status, statusText(r.status))

	// The host frames the response itself, so the guest must not also claim a
	// length or an encoding that contradicts what it actually wrote.
	r.header.Del("Transfer-Encoding")
	r.header.Set("Content-Length", strconv.Itoa(r.body.Len()))

	names := make([]string, 0, len(r.header))
	for name := range r.header {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		for _, value := range r.header[name] {
			fmt.Fprintf(&out, "%s: %s\r\n", name, value)
		}
	}
	out.WriteString("\r\n")
	_, _ = io.Copy(&out, &r.body)
	return out.Bytes()
}

func errorResponse(status int, detail string) []byte {
	body := detail + "\n"
	var out bytes.Buffer
	fmt.Fprintf(&out, "HTTP/1.1 %d %s\r\n", status, statusText(status))
	out.WriteString("Content-Type: text/plain; charset=utf-8\r\n")
	fmt.Fprintf(&out, "Content-Length: %d\r\n\r\n", len(body))
	out.WriteString(body)
	return out.Bytes()
}

func statusText(status int) string {
	if text := http.StatusText(status); text != "" {
		return text
	}
	return "Status"
}
