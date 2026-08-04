package gateway

import (
	"errors"
	"fmt"
	"io"
	"strings"
)

// term is a minimal line-oriented SSH UI (CRLF-friendly).
type term struct {
	rw     io.ReadWriter
	input  *migrationInput
	reader *migrationAttachment
	out    io.Writer
	skipLF bool
}

const maxLineBytes = 1024

func newTerm(rw io.ReadWriter) *term {
	input := newMigrationInput(rw, defaultMigrationBufferBytes)
	return &term{rw: rw, input: input, reader: input.Attach(), out: rw}
}

func (t *term) Printf(format string, args ...any) {
	fmt.Fprintf(t.out, strings.ReplaceAll(format, "\n", "\r\n"), args...)
}

func (t *term) ReadLine() (string, error) {
	line := make([]byte, 0, 64)
	for {
		b, err := t.readByte()
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
		b, err := t.readByte()
		if err != nil {
			return
		}
		if b == '\n' || b == '\r' {
			return
		}
	}
}

func (t *term) readByte() (byte, error) {
	var one [1]byte
	_, err := io.ReadFull(t.reader, one[:])
	return one[0], err
}

func (t *term) beginProxy() *migrationInput {
	if t.reader != nil {
		_ = t.reader.Close()
		t.reader = nil
	}
	return t.input
}

func (t *term) endProxy() {
	if t.reader == nil {
		t.reader = t.input.Attach()
	}
}
