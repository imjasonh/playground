package a

import "sync"

func bad(m sync.Mutex) { // want "passes lock by value: sync.Mutex"
	m.Lock()
}

func badRW(m sync.RWMutex) { // want "passes lock by value: sync.RWMutex"
	m.RLock()
}

func ok(m *sync.Mutex) {
	m.Lock()
}

func okWait(m *sync.WaitGroup) {
	m.Add(1)
}
