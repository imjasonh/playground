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
