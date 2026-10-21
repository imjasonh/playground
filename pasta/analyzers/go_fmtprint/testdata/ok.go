package ok

import (
	"fmt"
	"io"
	"log"
	"log/slog"
	"os"
)

func ok(w io.Writer, err error, name string) {
	fmt.Fprintf(w, "hello %s", name)
	fmt.Fprintln(os.Stderr, err)
	fmt.Fprintln(os.Stdout, "result")
	fmt.Fprint(os.Stdout, name)
	_ = fmt.Sprintf("hello %s", name)
	slog.Info("hello", "name", name)
	log.Fatal(err)
	log.Println(err)
}
