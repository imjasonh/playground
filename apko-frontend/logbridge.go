package main

import (
	"bytes"
	"context"
	"log/slog"
	"strings"
	"sync"

	"github.com/moby/buildkit/solver/pb"
)

// warnRangeKey is the attribute key that carries the source range a
// warning points at. warnHandler moves it into the warning instead of the
// message.
const warnRangeKey = "buildkit.range"

// warnHandler is a slog.Handler that reports each record at slog.LevelWarn
// or above to BuildKit as a build warning, and passes every record to next.
// The frontend installs it on the context with clog.WithLogger, so slog and
// clog calls in the frontend, and apko's own logging, reach the user.
//
// The warning's text is the message followed by the attributes in
// key=value form. An attribute with the key warnRangeKey and a []*pb.Range
// value sets the range in the configuration file that the warning points
// at; see warnRange.
type warnHandler struct {
	warn func(ctx context.Context, msg string, ranges []*pb.Range)
	next slog.Handler
	// text formats attributes. It shares buf, guarded by mu, with the
	// handlers that WithAttrs and WithGroup derive.
	text slog.Handler
	buf  *bytes.Buffer
	mu   *sync.Mutex
	// ranges holds a range attribute added with WithAttrs.
	ranges []*pb.Range
}

func newWarnHandler(warn func(ctx context.Context, msg string, ranges []*pb.Range), next slog.Handler) *warnHandler {
	buf := &bytes.Buffer{}
	return &warnHandler{
		warn: warn,
		next: next,
		text: slog.NewTextHandler(buf, &slog.HandlerOptions{
			ReplaceAttr: func(groups []string, a slog.Attr) slog.Attr {
				if len(groups) == 0 && (a.Key == slog.TimeKey || a.Key == slog.LevelKey || a.Key == slog.MessageKey) {
					return slog.Attr{}
				}
				return a
			},
		}),
		buf: buf,
		mu:  &sync.Mutex{},
	}
}

// warnRange returns an attribute that points a warning at the first line of
// data that contains s.
func warnRange(data []byte, s string) slog.Attr {
	for i, line := range strings.Split(string(data), "\n") {
		if strings.Contains(line, s) {
			pos := &pb.Position{Line: int32(i + 1)}
			return slog.Any(warnRangeKey, []*pb.Range{{Start: pos, End: pos}})
		}
	}
	return slog.Attr{}
}

func (h *warnHandler) Enabled(ctx context.Context, level slog.Level) bool {
	return level >= slog.LevelWarn || h.next.Enabled(ctx, level)
}

func (h *warnHandler) Handle(ctx context.Context, r slog.Record) error {
	if r.Level >= slog.LevelWarn {
		ranges := h.ranges
		rec := slog.NewRecord(r.Time, r.Level, r.Message, r.PC)
		r.Attrs(func(a slog.Attr) bool {
			if rs, ok := a.Value.Any().([]*pb.Range); ok && a.Key == warnRangeKey {
				ranges = rs
			} else {
				rec.AddAttrs(a)
			}
			return true
		})
		h.mu.Lock()
		h.buf.Reset()
		err := h.text.Handle(ctx, rec)
		attrs := strings.TrimSpace(h.buf.String())
		h.mu.Unlock()
		if err != nil {
			return err
		}
		msg := r.Message
		if attrs != "" {
			msg += " " + attrs
		}
		if r.Level >= slog.LevelError {
			msg = "error: " + msg
		}
		h.warn(ctx, msg, ranges)
		r = rec
	}
	if h.next.Enabled(ctx, r.Level) {
		return h.next.Handle(ctx, r)
	}
	return nil
}

func (h *warnHandler) WithAttrs(attrs []slog.Attr) slog.Handler {
	c := *h
	var keep []slog.Attr
	for _, a := range attrs {
		if rs, ok := a.Value.Any().([]*pb.Range); ok && a.Key == warnRangeKey {
			c.ranges = rs
		} else {
			keep = append(keep, a)
		}
	}
	c.text = h.text.WithAttrs(keep)
	c.next = h.next.WithAttrs(keep)
	return &c
}

func (h *warnHandler) WithGroup(name string) slog.Handler {
	c := *h
	c.text = h.text.WithGroup(name)
	c.next = h.next.WithGroup(name)
	return &c
}
