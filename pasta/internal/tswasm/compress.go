//go:build ignore

// Compresses ts-core.wasm → ts-core.wasm.br for go:embed.
package main

import (
	"log"
	"log/slog"
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
	slog.Info("wrote ts-core.wasm.br", "bytes", st.Size(), "from", len(in))
}

func fatal(err error) {
	log.Fatal(err)
}
