package a

import (
	"fmt"
	"io"
)

func bad(v string) {
	fmt.Printf("value \"%s\"\n", v)         // want "use %q"
	_ = fmt.Sprintf("value \"%s\"", v)      // want "use %q"
	_ = fmt.Errorf("missing \"%s\"", v)     // want "use %q"
	_ = fmt.Sprintf(`value "%s"`, v)        // want "use %q"
	fmt.Fprintf(io.Discard, "le=\"%s\"", v) // want "use %q"
	_ = fmt.Appendf(nil, "value \"%s\"", v) // want "use %q"
	fmt.Fprintf(io.Discard, `le="%s"`, v)   // want "use %q"
}

func ok(v string) string {
	fmt.Printf("value %q\n", v)
	fmt.Printf("%s\n", v)
	fmt.Fprintf(io.Discard, "le=%q", v)
	fmt.Fprintf(io.Discard, "%s=%q", "name", v)
	return fmt.Sprintf("%s", v)
}
