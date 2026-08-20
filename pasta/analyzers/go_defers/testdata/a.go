package a

import (
	"fmt"
	"time"
)

func bad(start time.Time) {
	defer fmt.Println(time.Since(start)) // want "call to time.Since is not deferred"
}

func ok(start time.Time) {
	defer func() {
		fmt.Println(time.Since(start))
	}()
}

func notDeferred(start time.Time) {
	fmt.Println(time.Since(start))
}
