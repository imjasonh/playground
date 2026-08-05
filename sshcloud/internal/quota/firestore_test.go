package quota

import (
	"context"
	"fmt"
	"os"
	"testing"
	"time"
)

func TestFirestoreRollingWindow(t *testing.T) {
	if os.Getenv("FIRESTORE_EMULATOR_HOST") == "" {
		t.Skip("FIRESTORE_EMULATOR_HOST not set")
	}
	project := os.Getenv("FIRESTORE_PROJECT_ID")
	if project == "" {
		project = "sshcloud-test"
	}
	prefix := fmt.Sprintf("quota_test_%d", time.Now().UnixNano())
	store, err := NewFirestore(context.Background(), project, prefix)
	if err != nil {
		t.Fatal(err)
	}
	defer store.Close()
	now := time.Now()
	limit := Limit{Max: 1, Window: time.Minute}
	req := Request{Kind: "join_ip", Subject: "192.0.2.1", EventID: "one", At: now, Limit: limit}
	if err := store.Take(context.Background(), req); err != nil {
		t.Fatal(err)
	}
	if err := store.Take(context.Background(), req); err != nil {
		t.Fatalf("idempotent event: %v", err)
	}
	req.EventID = "two"
	if err := store.Take(context.Background(), req); err == nil {
		t.Fatal("expected quota rejection")
	}
}
