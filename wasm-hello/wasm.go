//go:build wasip1

// The wasip1 face of the service: three exported functions and nothing else.
//
//	GOOS=wasip1 GOARCH=wasm go build -buildmode=c-shared -o hello.wasm .
//
// -buildmode=c-shared makes this a reactor module. The host starts the Go
// runtime once by calling _initialize, then calls http_handle per request, so
// the service — its goroutines, its heap, the counter in handler.Service —
// stays alive between requests instead of booting per request.
package main

import (
	"net/http"
	"unsafe"

	"github.com/imjasonh/playground/wasm-hello/handler"
	"github.com/imjasonh/playground/wasm-hello/wire"
)

// main never runs; a reactor module has no entry point. Go requires package
// main to declare one anyway.
func main() {}

var (
	service http.Handler = handler.New("")

	// Buffers whose lifetime the host depends on. Go's collector does not move
	// heap objects, so an offset into a slice stays valid for as long as
	// something reachable holds the slice — which is why these are package
	// level and not locals. responseBuffer in particular has to outlive the
	// return from http_handle: the host only reads it out of linear memory
	// once the call comes back.
	requestBuffer  []byte
	responseBuffer []byte
)

// http_alloc reserves size bytes inside the guest and returns the offset to
// write them at. One outstanding buffer at a time is all a request/response
// pair needs, which keeps the ABI at two calls and no free.
//
//go:wasmexport http_alloc
func httpAlloc(size uint32) uint32 {
	if size == 0 {
		requestBuffer = nil
		return 0
	}
	requestBuffer = make([]byte, size)
	return offsetOf(requestBuffer)
}

// http_handle serves one request and reports where the response landed, packed
// as offset<<32 | length so one i64 carries both.
//
// The region has to be the one http_alloc just returned. That is the contract
// the host follows anyway, and holding the guest to it means this can slice the
// buffer it already owns instead of manufacturing a pointer out of an integer
// the host supplied — which would be both unverifiable and a way to read any
// address in the module.
//
//go:wasmexport http_handle
func httpHandle(offset uint32, length uint32) uint64 {
	request, ok := allocatedRegion(offset, length)
	if !ok {
		return respond(wire.BadRequest("http_handle was given a region http_alloc did not return"))
	}
	return respond(wire.Serve(service, request))
}

// http_abi_version lets a host refuse a module whose calling convention it does
// not know, rather than discovering the mismatch as a garbled response.
//
//go:wasmexport http_abi_version
func httpABIVersion() uint32 { return 1 }

func allocatedRegion(offset uint32, length uint32) ([]byte, bool) {
	if len(requestBuffer) == 0 {
		return nil, false
	}
	if offset != offsetOf(requestBuffer) || int(length) > len(requestBuffer) {
		return nil, false
	}
	return requestBuffer[:length], true
}

func respond(response []byte) uint64 {
	responseBuffer = response
	if len(responseBuffer) == 0 {
		return 0
	}
	return uint64(offsetOf(responseBuffer))<<32 | uint64(len(responseBuffer))
}

// offsetOf is where a slice's bytes live in linear memory. Taking a slice's
// address is only meaningful because Go's collector does not move heap
// objects; the package-level references above are what keep these alive.
func offsetOf(buffer []byte) uint32 {
	return uint32(uintptr(unsafe.Pointer(&buffer[0])))
}
