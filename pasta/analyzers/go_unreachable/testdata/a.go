package a

import "fmt"

func afterReturn() {
	return // want "unreachable code"
	fmt.Println("dead")
}

func afterPanic() {
	panic("x") // want "unreachable code"
	fmt.Println("dead")
}

func ok() {
	if true {
		return
	}
	fmt.Println("reachable")
}

func okLast() {
	return
}
