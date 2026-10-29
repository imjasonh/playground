// Package fanout delivers click counts to the pages connected to this
// process.
//
// This app's Cloud Run config runs one writer at a time, so a click and its
// delivery happen in the same request, in the same process: the HTTP
// handler calls NotifyClick right after the durable write returns. That
// makes a SQL-level pub/sub mechanism unnecessary here — there is no other
// connection or process to signal. Delivery is in-memory and best effort: a
// page that misses a notification (a dropped connection, a restart) reads
// the correct count from the replica on its next connection, so nothing
// durable depends on this package. A different instance never calls
// NotifyClick for a click it did not handle; it reads the count from the
// replica on its own poll.
package fanout

import "sync"

// Click is one click count delivered to a subscriber.
type Click struct {
	// ID orders deliveries on one Hub. It has no meaning across hubs or
	// across a restart.
	ID int64
	// Count is the counters.clicks value already durable in the replica.
	Count int64
}

// Hub holds the subscribers waiting for clicks.
type Hub struct {
	mu      sync.Mutex
	nextSub uint64
	nextID  int64
	subs    map[uint64]chan Click
	closed  bool
}

// New returns an empty Hub.
func New() *Hub {
	return &Hub{subs: make(map[uint64]chan Click)}
}

// NotifyClick delivers count to every current subscriber. Call it after the
// write that produced count is durable.
func (h *Hub) NotifyClick(count int64) {
	h.mu.Lock()
	defer h.mu.Unlock()
	if h.closed {
		return
	}
	h.nextID++
	c := Click{ID: h.nextID, Count: count}
	for id, ch := range h.subs {
		select {
		case ch <- c:
		default:
			delete(h.subs, id)
			close(ch)
		}
	}
}

// Subscribe returns clicks delivered after this call, and a function that
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
	h.nextSub++
	id := h.nextSub
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

// Close stops delivery and closes every subscription.
func (h *Hub) Close() {
	h.mu.Lock()
	defer h.mu.Unlock()
	h.closed = true
	for id, ch := range h.subs {
		delete(h.subs, id)
		close(ch)
	}
}
