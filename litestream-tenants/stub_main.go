//go:build !vfs

package main

import (
	"fmt"
	"os"
)

func main() {
	fmt.Fprintln(os.Stderr, "litestream-tenants requires CGO and -tags vfs:")
	fmt.Fprintln(os.Stderr, "  CGO_ENABLED=1 go run -tags vfs . all")
	fmt.Fprintln(os.Stderr, "  CGO_ENABLED=1 go test -tags vfs ./...")
	os.Exit(2)
}
