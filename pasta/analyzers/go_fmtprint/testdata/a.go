package a

import "fmt"

func bad(err error, name string) {
	fmt.Println("hello")       // want "use slog"
	fmt.Print("hello")         // want "use slog"
	fmt.Printf("hello")        // want "use slog"
	fmt.Println(`hello`)       // want "use slog"
	defer fmt.Println("done")  // want "use slog"
	fmt.Println()              // want "use slog"
	fmt.Print()                // want "use slog"
	fmt.Println(err)           // want "use slog"
	fmt.Println("  " + name)   // want "use slog"
	fmt.Println("hello", err)  // want "use slog"
	fmt.Printf("hello %s", name) // want "use slog"
	fmt.Printf("hello %s")     // want "use slog"
}
