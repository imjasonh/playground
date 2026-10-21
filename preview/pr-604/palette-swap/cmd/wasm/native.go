//go:build !(js && wasm)

package main

import (
	"fmt"
	"io"
	"os"

	"github.com/imjasonh/playground/palette-swap"
)

func main() {
	writeCatalog(os.Stdout)
}

func writeCatalog(w io.Writer) {
	for _, p := range palette.Catalog {
		fmt.Fprintf(w, "%s\t%s\t%d\n", p.ID, p.Name, len(p.Colors))
	}
}
