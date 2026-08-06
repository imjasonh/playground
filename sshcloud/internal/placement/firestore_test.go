package placement

import (
	"context"
	"fmt"
	"os"
	"testing"
	"time"
)

func TestFirestoreRoundTrip(t *testing.T) {
	if os.Getenv("FIRESTORE_EMULATOR_HOST") == "" {
		t.Skip("FIRESTORE_EMULATOR_HOST not set; start the emulator to run this test")
	}
	ctx := context.Background()
	project := os.Getenv("FIRESTORE_PROJECT_ID")
	if project == "" {
		project = "sshcloud-test"
	}
	database := os.Getenv("PLACEMENT_FIRESTORE_DATABASE")
	if database == "" {
		database = "(default)"
	}
	fs, err := NewFirestoreDatabase(ctx, project, database, "sshcloud")
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = fs.Close() })

	user := fmt.Sprintf("u%d", time.Now().UnixNano())
	app := "fortune"
	if _, ok, err := fs.Get(ctx, user, app); err != nil || ok {
		t.Fatalf("empty get: ok=%v err=%v", ok, err)
	}
	if err := fs.SetIdentity(ctx, user, app, "host-a", "instance-a"); err != nil {
		t.Fatal(err)
	}
	h, ok, err := fs.Get(ctx, user, app)
	if err != nil || !ok || h != "host-a" {
		t.Fatalf("got %q ok=%v err=%v", h, ok, err)
	}
	now := time.Now()
	lease, err := fs.Acquire(ctx, user, app, "migration-test", time.Minute, now)
	if err != nil {
		t.Fatal(err)
	}
	if err := fs.Mark(ctx, lease, Operation{Kind: "migrate", SourceHost: "host-a", TargetHost: "host-b"}); err != nil {
		t.Fatal(err)
	}
	if err := fs.CommitStateIdentity(
		ctx, lease, "host-b", "instance-b", nil, now.Add(time.Second),
	); err != nil {
		t.Fatal(err)
	}
	h, ok, err = fs.Get(ctx, user, app)
	if err != nil || !ok || h != "host-b" {
		t.Fatalf("leased placement: got %q ok=%v err=%v", h, ok, err)
	}
	record, _, err := fs.GetRecord(ctx, user, app)
	if err != nil || record.Operation.Kind != "" {
		t.Fatalf("operation not cleared: %+v err=%v", record, err)
	}
	if err := fs.Delete(ctx, user, app); err != nil {
		t.Fatal(err)
	}
	if _, ok, _ := fs.Get(ctx, user, app); ok {
		t.Fatal("expected deleted")
	}
}
