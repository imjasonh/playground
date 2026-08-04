package gateway

import (
	"bufio"
	"errors"
	"fmt"
	"io"
	"strings"
)

// term is a minimal line-oriented SSH UI (CRLF-friendly).
type term struct {
	rw     io.ReadWriter
	in     *bufio.Reader
	out    io.Writer
	skipLF bool
}

const maxLineBytes = 1024

func newTerm(rw io.ReadWriter) *term {
	return &term{rw: rw, in: bufio.NewReader(rw), out: rw}
}

func (t *term) Printf(format string, args ...any) {
	fmt.Fprintf(t.out, strings.ReplaceAll(format, "\n", "\r\n"), args...)
}

func (t *term) ReadLine() (string, error) {
	line := make([]byte, 0, 64)
	for {
		b, err := t.in.ReadByte()
		if err != nil {
			return "", err
		}
		if t.skipLF {
			t.skipLF = false
			if b == '\n' {
				continue
			}
		}
		switch b {
		case '\r':
			t.skipLF = true
			return strings.TrimSpace(string(line)), nil
		case '\n':
			return strings.TrimSpace(string(line)), nil
		case 3: // Ctrl-C
			return "", errors.New("input cancelled")
		case '\b', 0x7f:
			if len(line) > 0 {
				line = line[:len(line)-1]
			}
		default:
			if len(line) >= maxLineBytes {
				t.discardLine()
				return "", fmt.Errorf("input exceeds %d bytes", maxLineBytes)
			}
			line = append(line, b)
		}
	}
}

func (t *term) discardLine() {
	for {
		b, err := t.in.ReadByte()
		if err != nil {
			return
		}
		if b == '\n' || b == '\r' {
			return
		}
	}
}
