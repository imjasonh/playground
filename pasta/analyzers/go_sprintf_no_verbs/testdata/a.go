package a

import "fmt"

func f() {
	_ = fmt.Sprintf("hello") // want "fmt.Sprintf with a constant string and no verbs is redundant"
	_ = fmt.Sprintf("hello %s", "world")
	_ = fmt.Sprintf("value: %d", 42)
}
