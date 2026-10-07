// Command buildflags prints the version that -ldflags sets and whether the
// foo build tag is on, for generate's tests.
package main

import "fmt"

var version = "unset"

func main() {
	fmt.Println(version, foo)
}
