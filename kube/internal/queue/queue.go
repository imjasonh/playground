// Package queue is a work queue for controllers.
//
// It has the guarantees controllers depend on: a key that's added many times
// before a worker takes it is processed once, a key is never processed by
// two workers at the same time, and a key added while it's being processed is
// processed again afterward. Failed keys back off exponentially, and keys
// can be scheduled for later.
//
// Keys have one of two priorities. High priority keys are always handed out
// before low priority keys, so a burst of low priority work (the initial
// list after a restart, or a periodic resync) doesn't delay reaction to real
// changes.
package queue

import (
	"container/heap"
	"container/list"
	"math/rand/v2"
	"sync"
	"time"
)

// Priority orders keys that are ready at the same time.
type Priority int

const (
	// Low is for work that doesn't come from a change, such as the initial
	// list of a cache or a periodic resync.
	Low Priority = iota
	// High is for changes.
	High
	numPriorities
)

// Options configure a Queue.
type Options struct {
	// BaseDelay is the first retry delay after a failure. It doubles with each
	// consecutive failure. The default is 50ms.
	BaseDelay time.Duration
	// MaxDelay caps the retry delay. The default is 5 minutes.
	MaxDelay time.Duration
	// Jitter adds up to this fraction of random delay to each retry, so keys
	// that fail together don't retry together. The default is 0.1. Set it to
	// a negative number to disable jitter.
	Jitter float64
}

// Queue is a deduplicating, prioritized work queue of keys.
type Queue[K comparable] struct {
	opts Options

	mu         sync.Mutex
	cond       *sync.Cond
	ready      [numPriorities]*list.List
	queued     map[K]*list.Element
	processing map[K]struct{}
	dirty      map[K]Priority
	failures   map[K]int
	waiting    waitHeap[K]
	waitIndex  map[K]*waitItem[K]
	shutdown   bool
	wake       chan struct{}
	stopped    chan struct{}
}

type entry[K comparable] struct {
	key K
	pri Priority
}

// New returns a running queue. Call ShutDown to stop it.
func New[K comparable](opts Options) *Queue[K] {
	if opts.BaseDelay <= 0 {
		opts.BaseDelay = 50 * time.Millisecond
	}
	if opts.MaxDelay <= 0 {
		opts.MaxDelay = 5 * time.Minute
	}
	if opts.Jitter == 0 {
		opts.Jitter = 0.1
	}
	q := &Queue[K]{
		opts:       opts,
		queued:     map[K]*list.Element{},
		processing: map[K]struct{}{},
		dirty:      map[K]Priority{},
		failures:   map[K]int{},
		waitIndex:  map[K]*waitItem[K]{},
		wake:       make(chan struct{}, 1),
		stopped:    make(chan struct{}),
	}
	q.cond = sync.NewCond(&q.mu)
	for i := range q.ready {
		q.ready[i] = list.New()
	}
	go q.delayLoop()
	return q
}

// Add makes key ready at priority p. Adding a key that's already waiting
// raises its priority if p is higher. Adding a key that's being processed
// queues it again for when processing finishes.
func (q *Queue[K]) Add(key K, p Priority) {
	q.mu.Lock()
	defer q.mu.Unlock()
	q.addLocked(key, p)
}

func (q *Queue[K]) addLocked(key K, p Priority) {
	if q.shutdown {
		return
	}
	if _, ok := q.processing[key]; ok {
		if old, ok := q.dirty[key]; !ok || p > old {
			q.dirty[key] = p
		}
		return
	}
	if el, ok := q.queued[key]; ok {
		e := el.Value.(entry[K])
		if p > e.pri {
			q.ready[e.pri].Remove(el)
			q.queued[key] = q.ready[p].PushBack(entry[K]{key, p})
		}
		return
	}
	q.queued[key] = q.ready[p].PushBack(entry[K]{key, p})
	q.cond.Signal()
}

// AddAfter makes key ready at priority p after d. If the key is already
// scheduled, the earlier time wins.
func (q *Queue[K]) AddAfter(key K, p Priority, d time.Duration) {
	if d <= 0 {
		q.Add(key, p)
		return
	}
	q.mu.Lock()
	defer q.mu.Unlock()
	if q.shutdown {
		return
	}
	at := time.Now().Add(d)
	if w, ok := q.waitIndex[key]; ok {
		if p > w.pri {
			w.pri = p
		}
		if at.Before(w.at) {
			w.at = at
			heap.Fix(&q.waiting, w.index)
		}
	} else {
		w := &waitItem[K]{key: key, at: at, pri: p}
		heap.Push(&q.waiting, w)
		q.waitIndex[key] = w
	}
	select {
	case q.wake <- struct{}{}:
	default:
	}
}

// Retry schedules key again after an exponential backoff that grows with
// each consecutive call. Call Forget when the key succeeds.
func (q *Queue[K]) Retry(key K, p Priority) time.Duration {
	q.mu.Lock()
	n := q.failures[key]
	q.failures[key] = n + 1
	q.mu.Unlock()
	d := q.opts.BaseDelay
	for i := 0; i < n && d < q.opts.MaxDelay; i++ {
		d *= 2
	}
	d = min(d, q.opts.MaxDelay)
	if q.opts.Jitter > 0 {
		d += time.Duration(rand.Float64() * q.opts.Jitter * float64(d)) // #nosec G404 -- jitter needs no cryptographic randomness.
	}
	q.AddAfter(key, p, d)
	return d
}

// RetryAfter schedules key again after d instead of the backoff. It counts
// the failure as Retry does, so a later Retry backs off from there.
func (q *Queue[K]) RetryAfter(key K, p Priority, d time.Duration) {
	q.mu.Lock()
	q.failures[key]++
	q.mu.Unlock()
	q.AddAfter(key, p, d)
}

// Failures returns how many consecutive times key has been retried.
func (q *Queue[K]) Failures(key K) int {
	q.mu.Lock()
	defer q.mu.Unlock()
	return q.failures[key]
}

// Forget resets the backoff for key.
func (q *Queue[K]) Forget(key K) {
	q.mu.Lock()
	delete(q.failures, key)
	q.mu.Unlock()
}

// Get blocks until a key is ready and marks it as being processed. Call Done
// when processing finishes. Get returns false after ShutDown.
func (q *Queue[K]) Get() (K, bool) {
	q.mu.Lock()
	defer q.mu.Unlock()
	for !q.shutdown && len(q.queued) == 0 {
		q.cond.Wait()
	}
	var zero K
	if q.shutdown {
		return zero, false
	}
	for p := numPriorities - 1; p >= 0; p-- {
		if el := q.ready[p].Front(); el != nil {
			q.ready[p].Remove(el)
			key := el.Value.(entry[K]).key
			delete(q.queued, key)
			q.processing[key] = struct{}{}
			return key, true
		}
	}
	return zero, false
}

// Done marks key as no longer being processed. If key was added while it was
// processing, it becomes ready again.
func (q *Queue[K]) Done(key K) {
	q.mu.Lock()
	defer q.mu.Unlock()
	delete(q.processing, key)
	if p, ok := q.dirty[key]; ok {
		delete(q.dirty, key)
		q.addLocked(key, p)
	}
}

// Len returns the number of keys that are ready, by priority.
func (q *Queue[K]) Len() (high, low int) {
	q.mu.Lock()
	defer q.mu.Unlock()
	return q.ready[High].Len(), q.ready[Low].Len()
}

// Waiting returns the number of keys scheduled for later.
func (q *Queue[K]) Waiting() int {
	q.mu.Lock()
	defer q.mu.Unlock()
	return len(q.waiting)
}

// ShutDown stops the queue. Blocked and future calls to Get return false.
func (q *Queue[K]) ShutDown() {
	q.mu.Lock()
	if !q.shutdown {
		q.shutdown = true
		close(q.wake)
	}
	q.cond.Broadcast()
	q.mu.Unlock()
	<-q.stopped
}

func (q *Queue[K]) delayLoop() {
	defer close(q.stopped)
	timer := time.NewTimer(time.Hour)
	defer timer.Stop()
	for {
		q.mu.Lock()
		if q.shutdown {
			q.mu.Unlock()
			return
		}
		now := time.Now()
		for len(q.waiting) > 0 && !q.waiting[0].at.After(now) {
			w := heap.Pop(&q.waiting).(*waitItem[K])
			delete(q.waitIndex, w.key)
			q.addLocked(w.key, w.pri)
		}
		next := time.Hour
		if len(q.waiting) > 0 {
			next = q.waiting[0].at.Sub(now)
		}
		q.mu.Unlock()
		timer.Reset(next)
		select {
		case <-timer.C:
		case _, ok := <-q.wake:
			if !ok {
				return
			}
		}
	}
}

type waitItem[K comparable] struct {
	key   K
	at    time.Time
	pri   Priority
	index int
}

type waitHeap[K comparable] []*waitItem[K]

func (h waitHeap[K]) Len() int           { return len(h) }
func (h waitHeap[K]) Less(i, j int) bool { return h[i].at.Before(h[j].at) }
func (h waitHeap[K]) Swap(i, j int) {
	h[i], h[j] = h[j], h[i]
	h[i].index, h[j].index = i, j
}
func (h *waitHeap[K]) Push(x any) {
	w := x.(*waitItem[K])
	w.index = len(*h)
	*h = append(*h, w)
}
func (h *waitHeap[K]) Pop() any {
	old := *h
	w := old[len(old)-1]
	old[len(old)-1] = nil
	*h = old[:len(old)-1]
	return w
}
