// Package par splits a loop over goroutines.
package par

import "sync"

// For calls fn over [0, n) in at most workers contiguous chunks, one
// goroutine per chunk, and returns when every call has returned. The chunks
// do not overlap, so fn may write to index ranges without locks.
func For(n, workers int, fn func(lo, hi int)) {
	if n <= 0 {
		return
	}
	if workers < 1 {
		workers = 1
	}
	if workers > n {
		workers = n
	}
	if workers == 1 {
		fn(0, n)
		return
	}
	var wg sync.WaitGroup
	for w := range workers {
		lo, hi := n*w/workers, n*(w+1)/workers
		wg.Go(func() { fn(lo, hi) })
	}
	wg.Wait()
}
