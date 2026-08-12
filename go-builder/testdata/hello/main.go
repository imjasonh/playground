package main

import (
	"fmt"
	"os"
)

func main() {
	fmt.Println("hello from go-builder")
	if v := os.Getenv("KO_DATA_PATH"); v != "" {
		fmt.Println("KO_DATA_PATH=" + v)
	}
}
