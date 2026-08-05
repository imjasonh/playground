package snapshot

import (
	"encoding/json"
	"strings"
	"testing"
)

func TestSnapshotSchemaFencesLayoutWithoutHostPath(t *testing.T) {
	t.Parallel()
	if SchemaVersion != 2 {
		t.Fatalf("SchemaVersion = %d, want 2 after jail layout migration", SchemaVersion)
	}
	content, err := json.Marshal(Meta{
		SchemaVersion: SchemaVersion,
		LayoutVersion: "firecracker-jailer-v1",
		User:          "alice",
		App:           "fortune",
	})
	if err != nil {
		t.Fatal(err)
	}
	encoded := string(content)
	if !strings.Contains(encoded, `"layout_version":"firecracker-jailer-v1"`) {
		t.Fatalf("metadata has no layout fence: %s", encoded)
	}
	if strings.Contains(encoded, "rootfs_path") || strings.Contains(encoded, "/var/lib") {
		t.Fatalf("metadata persisted an absolute host path: %s", encoded)
	}
}

func TestStructuredRefRoundTripAndGenerationIsolation(t *testing.T) {
	t.Parallel()
	first := Ref{User: "alice", App: "fortune", Gen: "g1"}
	second := Ref{User: "alice", App: "fortune", Gen: "g2"}
	if first.Key() == second.Key() {
		t.Fatal("different generations share a snapshot key")
	}
	got, err := ParseKey(first.Key())
	if err != nil {
		t.Fatal(err)
	}
	if got != first {
		t.Fatalf("ParseKey() = %+v, want %+v", got, first)
	}
	for _, invalid := range []string{"", "../alice", first.Key() + "/", strings.ToUpper(first.Key())} {
		if _, err := ParseKey(invalid); err == nil {
			t.Fatalf("ParseKey(%q) succeeded", invalid)
		}
	}
}
