package a

import "unsafe"

func bad(x uintptr) unsafe.Pointer {
	return unsafe.Pointer(uintptr(x)) // want "possible misuse of unsafe.Pointer"
}

func ok(x *int) unsafe.Pointer {
	return unsafe.Pointer(x)
}
