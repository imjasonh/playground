package substrate_test

import (
	"context"
	"net"
	"testing"

	ateapi "go.ate.dev/substrate/api/ateapi/v1"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/status"
	"google.golang.org/grpc/test/bufconn"

	"github.com/imjasonh/playground/ci-substrate/internal/substrate"
)

// fakeControl serves ListActors in two pages per atespace, and denies an
// atespace the caller has no role in.
type fakeControl struct {
	ateapi.UnimplementedControlServer
	actors map[string][]string // atespace -> uids
	denied map[string]bool
}

func (f *fakeControl) ListActors(_ context.Context, req *ateapi.ListActorsRequest) (*ateapi.ListActorsResponse, error) {
	if f.denied[req.GetAtespace()] {
		return nil, status.Error(codes.PermissionDenied, "no role")
	}
	uids := f.actors[req.GetAtespace()]
	page := &ateapi.ListActorsResponse{}
	from, to := 0, len(uids)/2
	if req.GetOptions().GetPageToken() == "second" {
		from, to = to, len(uids)
	} else if len(uids) > 1 {
		page.NextPageToken = "second"
	} else {
		to = len(uids)
	}
	for _, uid := range uids[from:to] {
		page.Actors = append(page.Actors, &ateapi.Actor{Metadata: &ateapi.ResourceMetadata{Atespace: req.GetAtespace(), Uid: uid}})
	}
	return page, nil
}

func TestDirectoryInAtespace(t *testing.T) {
	lis := bufconn.Listen(1 << 20)
	srv := grpc.NewServer()
	ateapi.RegisterControlServer(srv, &fakeControl{
		actors: map[string][]string{"tenant-a": {"a1", "a2", "a3", "a4"}, "tenant-b": {"b1"}},
		denied: map[string]bool{"tenant-c": true},
	})
	go srv.Serve(lis)
	t.Cleanup(srv.Stop)
	conn, err := grpc.NewClient("passthrough:///bufconn",
		grpc.WithContextDialer(func(context.Context, string) (net.Conn, error) { return lis.Dial() }),
		grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { conn.Close() })
	dir := substrate.NewDirectory(ateapi.NewControlClient(conn))

	for _, tc := range []struct {
		atespace, uid string
		want          bool
	}{
		{"tenant-a", "a1", true},
		{"tenant-a", "a4", true}, // on the second page
		{"tenant-a", "b1", false},
		{"tenant-b", "b1", true},
		{"tenant-b", "a1", false},
		{"tenant-z", "a1", false},
	} {
		got, err := dir.InAtespace(t.Context(), tc.atespace, tc.uid)
		if err != nil || got != tc.want {
			t.Errorf("InAtespace(%q, %q) = %v, %v; want %v", tc.atespace, tc.uid, got, err, tc.want)
		}
	}
	// No role in the atespace is an error, never "not there".
	if got, err := dir.InAtespace(t.Context(), "tenant-c", "a1"); err == nil || got {
		t.Errorf("InAtespace in a denied atespace = %v, %v; want an error", got, err)
	}
}
