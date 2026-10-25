// Command nosymbol exports no NewFilter symbol.
package main

import (
	"log/slog"
	"os"
)

func main() {
	slog.Error("nosymbol is a plugin", "build", "go build -buildmode=plugin -o nosymbol.so .")
	os.Exit(2)
}
