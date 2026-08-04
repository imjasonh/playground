package gateway

import (
	"bytes"
	"io"
	"testing"
	"time"
)

func TestMigrationInputReplaysBytesAcrossAttachments(t *testing.T) {
	t.Parallel()
	reader, writer := io.Pipe()
	buffer := newMigrationInput(reader, 1024)
	defer buffer.Close()
	first := buffer.Attach()
	if _, err := writer.Write([]byte("before")); err != nil {
		t.Fatal(err)
	}
	got := make([]byte, len("before"))
	if _, err := io.ReadFull(first, got); err != nil || string(got) != "before" {
		t.Fatalf("first read %q err=%v", got, err)
	}
	_ = first.Close()
	if _, err := writer.Write([]byte("frozen")); err != nil {
		t.Fatal(err)
	}
	second := buffer.Attach()
	got = make([]byte, len("frozen"))
	if _, err := io.ReadFull(second, got); err != nil || string(got) != "frozen" {
		t.Fatalf("replayed read %q err=%v", got, err)
	}
	_ = second.Close()
	_ = writer.Close()
}

func TestMigrationInputOverflow(t *testing.T) {
	t.Parallel()
	buffer := newMigrationInput(bytes.NewReader(bytes.Repeat([]byte("x"), 32)), 8)
	select {
	case <-buffer.Overflow():
	case <-time.After(time.Second):
		t.Fatal("overflow was not reported")
	}
	buffer.Close()
}
