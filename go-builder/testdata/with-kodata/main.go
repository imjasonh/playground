package main

import (
	"fmt"
	"os"
	"path/filepath"
)

func main() {
	root := os.Getenv("KO_DATA_PATH")
	b, err := os.ReadFile(filepath.Join(root, "message.txt"))
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	fmt.Print(string(b))
}
