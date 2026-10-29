package a

import (
	"fmt"

	. "strings" // want "dot import"
)

import . "os" // want "dot import"

func ok() {
	_ = fmt.Println
}
