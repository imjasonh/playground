package gateway

import (
	"bytes"
	"strings"
	"testing"
)

func TestTermReadLineHandlesCRAndEditing(t *testing.T) {
	t.Parallel()
	rw := &bufferReadWriter{reader: strings.NewReader("fortx\x7fune\rnext\r\nthird\n")}
	term := newTerm(rw)
	for i, want := range []string{"fortune", "next", "third"} {
		got, err := term.ReadLine()
		if err != nil {
			t.Fatalf("line %d: %v", i, err)
		}
		if got != want {
			t.Fatalf("line %d: got %q want %q", i, got, want)
		}
	}
}

func TestTermReadLineIsBounded(t *testing.T) {
	t.Parallel()
	rw := &bufferReadWriter{reader: strings.NewReader(strings.Repeat("x", maxLineBytes+1) + "\nok\n")}
	term := newTerm(rw)
	if _, err := term.ReadLine(); err == nil {
		t.Fatal("expected oversized line error")
	}
	got, err := term.ReadLine()
	if err != nil || got != "ok" {
		t.Fatalf("next line: %q, %v", got, err)
	}
}

type bufferReadWriter struct {
	reader *strings.Reader
	writer bytes.Buffer
}

func (rw *bufferReadWriter) Read(p []byte) (int, error)  { return rw.reader.Read(p) }
func (rw *bufferReadWriter) Write(p []byte) (int, error) { return rw.writer.Write(p) }
