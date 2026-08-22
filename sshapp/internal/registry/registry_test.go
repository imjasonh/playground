package registry_test

import (
	"errors"
	"io"
	"strings"
	"testing"

	"github.com/imjasonh/playground/sshapp/internal/registry"
)

func TestPickByNumber(t *testing.T) {
	t.Parallel()
	cat := registry.FromNames([]string{"hello", "other"})
	var out strings.Builder
	got, err := cat.Pick(strings.NewReader("1\n"), &out)
	if err != nil {
		t.Fatal(err)
	}
	if got.Name != "hello" {
		t.Fatalf("got %q", got.Name)
	}
	if !strings.Contains(out.String(), "1) hello") {
		t.Fatalf("menu = %q", out.String())
	}
}

func TestPickByName(t *testing.T) {
	t.Parallel()
	cat := registry.FromNames([]string{"hello", "other"})
	got, err := cat.Pick(strings.NewReader("other\n"), io.Discard)
	if err != nil || got.Name != "other" {
		t.Fatalf("got %+v err=%v", got, err)
	}
}

func TestPickCancel(t *testing.T) {
	t.Parallel()
	cat := registry.FromNames([]string{"hello"})
	_, err := cat.Pick(strings.NewReader("q\n"), io.Discard)
	if !errors.Is(err, registry.ErrCanceled) {
		t.Fatalf("err = %v", err)
	}
}

func TestPickUnknown(t *testing.T) {
	t.Parallel()
	cat := registry.FromNames([]string{"hello"})
	if _, err := cat.Pick(strings.NewReader("nope\n"), io.Discard); err == nil {
		t.Fatal("expected error")
	}
}
