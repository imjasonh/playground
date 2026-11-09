package objstore_test

import (
	"bytes"
	"errors"
	"fmt"
	"net/http/httptest"
	"slices"
	"strings"
	"sync"
	"testing"

	"github.com/imjasonh/playground/cloudrun-duckdb/internal/fakegcs"
	"github.com/imjasonh/playground/cloudrun-duckdb/internal/objstore"
)

func backends(t *testing.T) map[string]objstore.Bucket {
	t.Helper()
	file, err := objstore.Open(t.Context(), "file://"+t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	srv := httptest.NewServer(fakegcs.New(t.TempDir(), fakegcs.Latency{}))
	t.Cleanup(srv.Close)
	gcs, err := objstore.Open(t.Context(), "gs://bucket/some/prefix?endpoint="+srv.URL)
	if err != nil {
		t.Fatal(err)
	}
	return map[string]objstore.Bucket{"file": file, "gcs": gcs}
}

func keys(objs []objstore.Object) []string {
	var out []string
	for _, o := range objs {
		out = append(out, o.Key)
	}
	return out
}

func TestBucket(t *testing.T) {
	for name, b := range backends(t) {
		t.Run(name, func(t *testing.T) {
			ctx := t.Context()
			if _, err := b.Get(ctx, "log/1"); !errors.Is(err, objstore.ErrNotFound) {
				t.Fatalf("Get missing: %v, want ErrNotFound", err)
			}
			for _, k := range []string{"log/3", "log/1", "log/2", "base/1"} {
				if err := b.Create(ctx, k, strings.NewReader("v"+k), int64(len("v"+k))); err != nil {
					t.Fatalf("Create %s: %v", k, err)
				}
			}
			if err := b.Create(ctx, "log/2", strings.NewReader("other"), 5); !errors.Is(err, objstore.ErrExists) {
				t.Fatalf("Create existing: %v, want ErrExists", err)
			}
			got, err := objstore.ReadAll(ctx, b, "log/2")
			if err != nil || string(got) != "vlog/2" {
				t.Fatalf("Get log/2 = %q, %v", got, err)
			}
			objs, err := b.List(ctx, "log/", "")
			if err != nil {
				t.Fatal(err)
			}
			if want := []string{"log/1", "log/2", "log/3"}; !slices.Equal(keys(objs), want) {
				t.Fatalf("List = %v, want %v", keys(objs), want)
			}
			if objs[0].Size != 6 || objs[0].Created.IsZero() {
				t.Fatalf("List entry %+v lacks size or creation time", objs[0])
			}
			objs, err = b.List(ctx, "log/", "log/1")
			if err != nil {
				t.Fatal(err)
			}
			if want := []string{"log/2", "log/3"}; !slices.Equal(keys(objs), want) {
				t.Fatalf("List after log/1 = %v, want %v", keys(objs), want)
			}
			if err := b.Delete(ctx, "log/1"); err != nil {
				t.Fatal(err)
			}
			if err := b.Delete(ctx, "log/1"); err != nil {
				t.Fatalf("Delete missing: %v", err)
			}
			objs, _ = b.List(ctx, "log/", "")
			if want := []string{"log/2", "log/3"}; !slices.Equal(keys(objs), want) {
				t.Fatalf("List after delete = %v, want %v", keys(objs), want)
			}
		})
	}
}

// TestCreateRace checks that exactly one of many concurrent creates of one
// key wins.
func TestCreateRace(t *testing.T) {
	for name, b := range backends(t) {
		t.Run(name, func(t *testing.T) {
			var wg sync.WaitGroup
			var mu sync.Mutex
			var wins []int
			for i := range 16 {
				wg.Go(func() {
					body := fmt.Sprint(i)
					err := b.Create(t.Context(), "log/race", strings.NewReader(body), int64(len(body)))
					switch {
					case err == nil:
						mu.Lock()
						wins = append(wins, i)
						mu.Unlock()
					case !errors.Is(err, objstore.ErrExists):
						t.Errorf("create %d: %v", i, err)
					}
				})
			}
			wg.Wait()
			if len(wins) != 1 {
				t.Fatalf("%d creates won: %v", len(wins), wins)
			}
			got, _ := objstore.ReadAll(t.Context(), b, "log/race")
			if string(got) != fmt.Sprint(wins[0]) {
				t.Fatalf("object holds %q, winner wrote %d", got, wins[0])
			}
		})
	}
}

func TestListPages(t *testing.T) {
	srv := httptest.NewServer(fakegcs.New(t.TempDir(), fakegcs.Latency{}))
	t.Cleanup(srv.Close)
	b, err := objstore.Open(t.Context(), "gs://bucket/db?endpoint="+srv.URL)
	if err != nil {
		t.Fatal(err)
	}
	var want []string
	for i := range 2500 {
		k := fmt.Sprintf("log/%05d", i)
		want = append(want, k)
		if err := b.Create(t.Context(), k, bytes.NewReader([]byte{1}), 1); err != nil {
			t.Fatal(err)
		}
	}
	objs, err := b.List(t.Context(), "log/", "")
	if err != nil {
		t.Fatal(err)
	}
	if !slices.Equal(keys(objs), want) {
		t.Fatalf("listed %d keys across pages, want %d", len(objs), len(want))
	}
}
