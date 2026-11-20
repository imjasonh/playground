package a

import "time"

func f(ch chan int) {
	// Good: select outside loop
	select {
	case <-time.After(time.Second):
	case <-ch:
	}

	// Bad: select inside loop
	for i := 0; i < 10; i++ {
		select {
		case <-time.After(time.Second): // want "time.After in a for-select loop will leak memory"
		case <-ch:
		}
	}
}
