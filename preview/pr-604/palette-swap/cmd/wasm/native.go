//go:build !(js && wasm)

package main

import (
	"fmt"
	"os"

	"github.com/imjasonh/playground/palette-swap"
)

func main() {
	for _, p := range palette.Catalog {
		fmt.Fprintf(os.Stdout, "%s\t%s\t%d\n", p.ID, p.Name, len(p.Colors))
	}
}
