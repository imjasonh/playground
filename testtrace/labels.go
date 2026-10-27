package testtrace

import "unsafe"

// getProfLabel returns the current goroutine's profiler label pointer. The
// runtime copies that pointer into every goroutine that the goroutine
// starts, so it identifies a goroutine and all of its descendants. The
// runtime keeps this linkname for external packages (see the "hall of
// shame" note in runtime/proflabel.go), so the linker allows it.
//
//go:linkname getProfLabel runtime/pprof.runtime_getProfLabel
func getProfLabel() unsafe.Pointer
