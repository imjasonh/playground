// Package honk publishes click counts through Honker and delivers them to
// subscribers in this process.
//
// The Litestream database is one SQLite connection. A second connection
// would be a second VFS, with its own page cache and write buffer, and
// Honker's listener has to poll while requests run. honker.db is an ordinary
// SQLite file in the instance scratch directory. Litestream does not
// replicate it. Listeners on this process wake from that file. Another
// instance has its own file.
package honk

import (
	"context"
	"encoding/json"
	"errors"
	"log/slog"
	"sync"
	"time"

	"github.com/russellromney/honker-go"
)

// Click is one committed click count.
type Click struct {
	// ID is the Honker notification row id. Startup writes a probe row on
	// the same channel, so the first click's id can be greater than 1.
	ID int64
	// Count is the counters.clicks value stored in the replica.
	Count int64
}

// Hub is a Honker database and the subscribers waiting on its clicks channel.
type Hub struct {
	db       *honker.Database
	cancel   context.CancelFunc
	done     chan struct{}
	armed    chan struct{}
	armOnce  sync.Once
	notifyMu sync.Mutex

	closeOnce sync.Once
	closeErr  error

	mu     sync.Mutex
	next   uint64
	subs   map[uint64]chan Click
	closed bool
}

// Open opens a Honker database at path, loading the extension at
// extensionPath. Open returns after Listen is waiting, which it checks by
// writing a probe notification. A notification written before Listen records
// its starting id is skipped, so Open repeats the probe until one arrives.
func Open(ctx context.Context, path, extensionPath string) (*Hub, error) {
	db, err := honker.Open(path, extensionPath)
	if err != nil {
		return nil, err
	}
	ctx, cancel := context.WithCancel(ctx)
	h := &Hub{
		db:     db,
		cancel: cancel,
		done:   make(chan struct{}),
		armed:  make(chan struct{}),
		subs:   make(map[uint64]chan Click),
	}
	go func() {
		defer close(h.done)
		h.loop(ctx)
	}()
	if err := h.arm(ctx); err != nil {
		h.Close()
		return nil, err
	}
	return h, nil
}

func (h *Hub) arm(ctx context.Context) error {
	deadline, stop := context.WithTimeout(ctx, 5*time.Second)
	defer stop()
	tick := time.NewTicker(20 * time.Millisecond)
	defer tick.Stop()
	for {
		if _, err := h.db.Notify("clicks", map[string]any{"ready": true}); err != nil {
			return err
		}
		select {
		case <-h.armed:
			return nil
		case <-deadline.Done():
			if err := ctx.Err(); err != nil {
				return err
			}
			return errors.New("honker listener did not start")
		case <-tick.C:
		}
	}
}

// Close stops the listener and closes the database. Further calls return
// the first error.
func (h *Hub) Close() error {
	h.closeOnce.Do(func() {
		h.cancel()
		h.closeErr = h.db.Close()
		<-h.done
		h.mu.Lock()
		defer h.mu.Unlock()
		h.closed = true
		for id, ch := range h.subs {
			delete(h.subs, id)
			close(ch)
		}
	})
	return h.closeErr
}

// NotifyClick inserts a notification for count. Call it after the replica
// has the count. Concurrent calls are serialized. Delivery order still
// follows whichever request reaches this call first.
func (h *Hub) NotifyClick(count int64) error {
	h.notifyMu.Lock()
	defer h.notifyMu.Unlock()
	_, err := h.db.Notify("clicks", map[string]any{"count": count})
	return err
}

// Subscribe returns clicks published after this call, and a function that
// removes the subscription. The channel closes when the hub closes or the
// unsubscribe function runs.
func (h *Hub) Subscribe() (<-chan Click, func()) {
	h.mu.Lock()
	defer h.mu.Unlock()
	if h.closed {
		ch := make(chan Click)
		close(ch)
		return ch, func() {}
	}
	h.next++
	id := h.next
	ch := make(chan Click, 32)
	h.subs[id] = ch
	return ch, func() { h.remove(id) }
}

func (h *Hub) remove(id uint64) {
	h.mu.Lock()
	defer h.mu.Unlock()
	ch, ok := h.subs[id]
	if !ok {
		return
	}
	delete(h.subs, id)
	close(ch)
}

func (h *Hub) loop(ctx context.Context) {
	for note := range h.db.Listen(ctx, "clicks") {
		var body struct {
			Count int64 `json:"count"`
			Ready bool  `json:"ready"`
		}
		if err := json.Unmarshal(note.Payload, &body); err != nil {
			slog.Warn("honker notification", "error", err, "id", note.ID)
			continue
		}
		if body.Ready {
			h.armOnce.Do(func() { close(h.armed) })
			continue
		}
		h.broadcast(Click{ID: note.ID, Count: body.Count})
	}
}

func (h *Hub) broadcast(c Click) {
	h.mu.Lock()
	defer h.mu.Unlock()
	if h.closed {
		return
	}
	for id, ch := range h.subs {
		select {
		case ch <- c:
		default:
			delete(h.subs, id)
			close(ch)
		}
	}
}
