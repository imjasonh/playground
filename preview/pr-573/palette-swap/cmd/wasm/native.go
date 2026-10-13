//go:build !(js && wasm)

package main

import (
	"fmt"

	"github.com/imjasonh/playground/palette-swap"
)

func main() {
	for _, p := range palette.Catalog {
		fmt.Printf("%s\t%s\t%d\n", p.ID, p.Name, len(p.Colors))
	}
}
