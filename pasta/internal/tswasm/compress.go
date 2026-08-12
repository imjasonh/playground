//go:build ignore

// Compresses ts-core.wasm → ts-core.wasm.br for go:embed.
package main

import (
	"fmt"
	"os"

	"github.com/andybalholm/brotli"
)

func main() {
	in, err := os.ReadFile("ts-core.wasm")
	if err != nil {
		fatal(err)
	}
	f, err := os.Create("ts-core.wasm.br")
	if err != nil {
		fatal(err)
	}
	w := brotli.NewWriterLevel(f, brotli.BestCompression)
	if _, err := w.Write(in); err != nil {
		fatal(err)
	}
	if err := w.Close(); err != nil {
		fatal(err)
	}
	if err := f.Close(); err != nil {
		fatal(err)
	}
	st, _ := os.Stat("ts-core.wasm.br")
	fmt.Printf("wrote ts-core.wasm.br (%d bytes from %d)\n", st.Size(), len(in))
}

func fatal(err error) {
	fmt.Fprintln(os.Stderr, err)
	os.Exit(1)
}
