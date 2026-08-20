package a

import "fmt"

func bad() {
	fmt.Printf("hello %s") // want "format has a verb but no operand"
	fmt.Sprintf("%d")      // want "format has a verb but no operand"
	fmt.Errorf("x %v")     // want "format has a verb but no operand"
}

func ok() {
	fmt.Printf("hello %s", "world")
	fmt.Printf("hello")
	fmt.Println("%s")
}
