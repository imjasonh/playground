package gateway

import (
	"bytes"
	"io"
	"os"
	"path/filepath"
	"runtime"
	"strings"
	"testing"
)

func TestMigrationReplayIsTransportOnlyAndUnobservable(t *testing.T) {
	sentinel := []byte("SSH_STDIN_REPLAY_SENTINEL")
	input := newMigrationInput(bytes.NewReader(sentinel), len(sentinel)+1)
	attachment := input.Attach()
	replayed, err := io.ReadAll(attachment)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(replayed, sentinel) {
		t.Fatalf("replayed bytes = %q, want exact transport continuity", replayed)
	}

	_, currentFile, _, _ := runtime.Caller(0)
	source, err := os.ReadFile(filepath.Join(filepath.Dir(currentFile), "migration_buffer.go"))
	if err != nil {
		t.Fatal(err)
	}
	for _, forbidden := range []string{"log.", "slog.", "observability.", "telemetry."} {
		if strings.Contains(string(source), forbidden) {
			t.Fatalf("migration replay buffer became observable through %q", forbidden)
		}
	}
}
