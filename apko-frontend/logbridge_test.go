package main

import (
	"bytes"
	"context"
	"log/slog"
	"strings"
	"sync"
	"testing"

	"github.com/chainguard-dev/clog"
	"github.com/moby/buildkit/solver/pb"
)

type warning struct {
	msg    string
	ranges []*pb.Range
}

func newTestLogger(t *testing.T) (context.Context, *bytes.Buffer, func() []warning) {
	t.Helper()
	var mu sync.Mutex
	var got []warning
	var stderr bytes.Buffer
	next := slog.NewTextHandler(&stderr, &slog.HandlerOptions{Level: slog.LevelInfo})
	h := newWarnHandler(func(_ context.Context, msg string, ranges []*pb.Range) {
		mu.Lock()
		defer mu.Unlock()
		got = append(got, warning{msg, ranges})
	}, next)
	ctx := clog.WithLogger(t.Context(), clog.New(h))
	return ctx, &stderr, func() []warning {
		mu.Lock()
		defer mu.Unlock()
		return append([]warning(nil), got...)
	}
}

func TestWarnHandler(t *testing.T) {
	ctx, stderr, warnings := newTestLogger(t)
	log := clog.FromContext(ctx)

	log.Info("resolving", "packages", 3)
	log.Warn("missing key", "key", "a.rsa.pub")
	log.With("repo", "https://example.com/os").WithGroup("index").Warn("stale", "age", "2h")
	log.Error("failed", "err", "boom")
	slog.New(clog.FromContext(ctx).Handler()).Warn("from slog")

	want := []string{
		`missing key key=a.rsa.pub`,
		`stale repo=https://example.com/os index.age=2h`,
		`error: failed err=boom`,
		`from slog`,
	}
	var got []string
	for _, w := range warnings() {
		got = append(got, w.msg)
	}
	if strings.Join(got, "\n") != strings.Join(want, "\n") {
		t.Errorf("warnings:\n%s\nwant:\n%s", strings.Join(got, "\n"), strings.Join(want, "\n"))
	}
	if !strings.Contains(stderr.String(), "msg=resolving packages=3") {
		t.Errorf("stderr is missing the info record:\n%s", stderr)
	}
	if !strings.Contains(stderr.String(), `msg="missing key"`) {
		t.Errorf("stderr is missing the warning record:\n%s", stderr)
	}
}

func TestWarnHandlerRange(t *testing.T) {
	ctx, stderr, warnings := newTestLogger(t)
	data := []byte("contents:\n  keyring:\n    - http://example.com/key.rsa.pub\n")
	clog.FromContext(ctx).Warn("insecure keyring", warnRange(data, "http://example.com/key.rsa.pub"))

	ws := warnings()
	if len(ws) != 1 {
		t.Fatalf("got %d warnings, want 1", len(ws))
	}
	if ws[0].msg != "insecure keyring" {
		t.Errorf("message = %q, want the range left out", ws[0].msg)
	}
	if len(ws[0].ranges) != 1 || ws[0].ranges[0].Start.Line != 3 {
		t.Errorf("ranges = %v, want line 3", ws[0].ranges)
	}
	if strings.Contains(stderr.String(), warnRangeKey) {
		t.Errorf("stderr has the range attribute:\n%s", stderr)
	}
}

func TestWarnHandlerConcurrent(t *testing.T) {
	ctx, _, warnings := newTestLogger(t)
	var wg sync.WaitGroup
	for i := range 20 {
		wg.Go(func() {
			clog.FromContext(ctx).Warn("w", "i", i)
		})
	}
	wg.Wait()
	for _, w := range warnings() {
		if !strings.HasPrefix(w.msg, "w i=") || strings.Count(w.msg, "i=") != 1 {
			t.Errorf("warning %q mixes records", w.msg)
		}
	}
	if n := len(warnings()); n != 20 {
		t.Errorf("got %d warnings, want 20", n)
	}
}
