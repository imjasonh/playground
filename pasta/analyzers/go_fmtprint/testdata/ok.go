package ok

import (
	"fmt"
	"io"
	"log"
	"log/slog"
)

func ok(w io.Writer, err error, name string) {
	// w is the writer the caller passed.
	fmt.Fprintf(w, "hello %s", name)
	fmt.Fprintln(w, err)
	_ = fmt.Sprintf("hello %s", name)
	slog.Info("hello", "name", name)
	log.Fatal(err)
	log.Println(err)
}
