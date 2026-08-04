package gateway

import (
	"bufio"
	"fmt"
	"io"
	"strings"
)

// term is a minimal line-oriented SSH UI (CRLF-friendly).
type term struct {
	in  *bufio.Reader
	out io.Writer
}

func newTerm(rw io.ReadWriter) *term {
	return &term{in: bufio.NewReader(rw), out: rw}
}

func (t *term) Printf(format string, args ...any) {
	fmt.Fprintf(t.out, strings.ReplaceAll(format, "\n", "\r\n"), args...)
}

func (t *term) ReadLine() (string, error) {
	line, err := t.in.ReadString('\n')
	if err != nil {
		return "", err
	}
	line = strings.TrimSuffix(line, "\n")
	line = strings.TrimSuffix(line, "\r")
	return strings.TrimSpace(line), nil
}
