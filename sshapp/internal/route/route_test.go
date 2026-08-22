package route_test

import (
	"testing"

	"github.com/imjasonh/playground/sshapp/internal/route"
)

type fakeSession struct {
	environ   []string
	command   []string
	subsystem string
}

func (f *fakeSession) Environ() []string { return f.environ }
func (f *fakeSession) Command() []string { return f.command }
func (f *fakeSession) Subsystem() string { return f.subsystem }

func TestFromSessionEnvWins(t *testing.T) {
	t.Parallel()
	got, ok := route.FromSession(&fakeSession{
		environ: []string{"SSHAPP=hello.example.com"},
		command: []string{"ignored"},
	})
	if !ok || got.App != "hello" {
		t.Fatalf("got %+v ok=%v", got, ok)
	}
}

func TestFromSessionCommandPath(t *testing.T) {
	t.Parallel()
	got, ok := route.FromSession(&fakeSession{
		command: []string{"foo/bar", "--flag"},
	})
	if !ok || got.App != "foo" {
		t.Fatalf("app = %+v", got)
	}
	if len(got.Args) != 2 || got.Args[0] != "bar" || got.Args[1] != "--flag" {
		t.Fatalf("args = %#v", got.Args)
	}
}

func TestFromSessionSubsystem(t *testing.T) {
	t.Parallel()
	got, ok := route.FromSession(&fakeSession{subsystem: "hello"})
	if !ok || got.App != "hello" {
		t.Fatalf("got %+v ok=%v", got, ok)
	}
}

func TestFromSessionMissing(t *testing.T) {
	t.Parallel()
	if _, ok := route.FromSession(&fakeSession{}); ok {
		t.Fatal("expected no target")
	}
}
