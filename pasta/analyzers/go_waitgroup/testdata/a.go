package a

import "sync"

func bad(wg *sync.WaitGroup) {
	go func() { // want "WaitGroup.Add called from inside new goroutine"
		wg.Add(1)
		wg.Done()
	}()
}

func ok(wg *sync.WaitGroup) {
	wg.Add(1)
	go func() {
		defer wg.Done()
	}()
}

func okLater(wg *sync.WaitGroup) {
	go func() {
		wg.Done()
		wg.Add(1)
	}()
}
