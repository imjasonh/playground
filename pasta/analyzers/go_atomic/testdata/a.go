package a

import "sync/atomic"

func bad(x int32) {
	x = atomic.AddInt32(&x, 1) // want "direct assignment to atomic value"
}

func okStore(x int32) {
	atomic.AddInt32(&x, 1)
}

func okOther(x, y int32) {
	y = atomic.AddInt32(&x, 1)
}
