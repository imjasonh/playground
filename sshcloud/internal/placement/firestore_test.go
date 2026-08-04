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
	fs, err := NewFirestore(ctx, project)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = fs.Close() })

	user := fmt.Sprintf("u%d", time.Now().UnixNano())
	app := "fortune"
	if _, ok, err := fs.Get(ctx, user, app); err != nil || ok {
		t.Fatalf("empty get: ok=%v err=%v", ok, err)
	}
	if err := fs.Set(ctx, user, app, "host-a"); err != nil {
		t.Fatal(err)
	}
	h, ok, err := fs.Get(ctx, user, app)
	if err != nil || !ok || h != "host-a" {
		t.Fatalf("got %q ok=%v err=%v", h, ok, err)
	}
	if err := fs.Delete(ctx, user, app); err != nil {
		t.Fatal(err)
	}
	if _, ok, _ := fs.Get(ctx, user, app); ok {
		t.Fatal("expected deleted")
	}
}
