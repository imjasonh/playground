package litevfs

import (
	"bytes"
	"cmp"
	"context"
	"encoding/binary"
	"errors"
	"fmt"
	"io"
	"log/slog"
	"math/rand"
	"os"
	"path/filepath"
	"slices"
	"strconv"
	"strings"
	"sync"
	"testing"
	"time"

	// sqlite3vfs calls into the SQLite C library, which go-sqlite3 links.
	_ "github.com/mattn/go-sqlite3"
	"github.com/psanford/sqlite3vfs"
	"github.com/superfly/ltx"
)

// The tests in this file drive a writable VFSFile without SQLite. Polls and
// compactions run on their own goroutines, but each storage call they make
// pauses until the test resumes the task, so the test picks the exact order
// of those calls relative to writes, syncs, and reads. Only one goroutine runs
// VFS code at a time, so a seed replays the same schedule.
//
// Every page read is compared with the last version the test wrote, which
// fails a run at the read that returned a stale page instead of seconds later
// when SQLite reaches a broken b-tree.

const (
	ilPageSize = DefaultPageSize
	ilMaxPages = 24
)

// memClient is an in-memory ReplicaClient. Calls made with a context from
// harness.start pause before and after each listing and before each upload
// is stored.
type memClient struct {
	mu    sync.Mutex
	files map[int][]*ltx.FileInfo
	data  map[memKey][]byte
}

type memKey struct {
	level            int
	minTXID, maxTXID ltx.TXID
}

func newMemClient() *memClient {
	return &memClient{files: make(map[int][]*ltx.FileInfo), data: make(map[memKey][]byte)}
}

func (c *memClient) Type() string               { return "mem" }
func (c *memClient) Init(context.Context) error { return nil }
func (c *memClient) SetLogger(*slog.Logger)     {}

func (c *memClient) LTXFiles(ctx context.Context, level int, seek ltx.TXID, _ bool) (ltx.FileIterator, error) {
	pause(ctx, "list L%d", level)
	c.mu.Lock()
	var a []*ltx.FileInfo
	for _, info := range c.files[level] {
		if info.MinTXID >= seek {
			info := *info
			a = append(a, &info)
		}
	}
	c.mu.Unlock()
	slices.SortFunc(a, func(x, y *ltx.FileInfo) int { return cmp.Compare(x.MinTXID, y.MinTXID) })
	// A pause here models a listing that reaches the caller late.
	pause(ctx, "listed L%d", level)
	return ltx.NewFileInfoSliceIterator(a), nil
}

func (c *memClient) OpenLTXFile(_ context.Context, level int, minTXID, maxTXID ltx.TXID, offset, size int64) (io.ReadCloser, error) {
	c.mu.Lock()
	b, ok := c.data[memKey{level, minTXID, maxTXID}]
	c.mu.Unlock()
	if !ok {
		return nil, os.ErrNotExist
	}
	b = b[min(offset, int64(len(b))):]
	if size > 0 && size < int64(len(b)) {
		b = b[:size]
	}
	return io.NopCloser(bytes.NewReader(b)), nil
}

func (c *memClient) WriteLTXFile(ctx context.Context, level int, minTXID, maxTXID ltx.TXID, r io.Reader) (*ltx.FileInfo, error) {
	b, err := io.ReadAll(r)
	if err != nil {
		return nil, err
	}
	pause(ctx, "write L%d", level)
	info := &ltx.FileInfo{Level: level, MinTXID: minTXID, MaxTXID: maxTXID, Size: int64(len(b)), CreatedAt: time.Now()}
	c.mu.Lock()
	defer c.mu.Unlock()
	c.removeLocked(level, minTXID, maxTXID)
	c.files[level] = append(c.files[level], info)
	c.data[memKey{level, minTXID, maxTXID}] = b
	out := *info
	return &out, nil
}

func (c *memClient) DeleteLTXFiles(_ context.Context, a []*ltx.FileInfo) error {
	c.mu.Lock()
	defer c.mu.Unlock()
	for _, info := range a {
		c.removeLocked(info.Level, info.MinTXID, info.MaxTXID)
	}
	return nil
}

func (c *memClient) DeleteAll(context.Context) error {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.files = make(map[int][]*ltx.FileInfo)
	c.data = make(map[memKey][]byte)
	return nil
}

func (c *memClient) removeLocked(level int, minTXID, maxTXID ltx.TXID) {
	delete(c.data, memKey{level, minTXID, maxTXID})
	c.files[level] = slices.DeleteFunc(c.files[level], func(info *ltx.FileInfo) bool {
		return info.MinTXID == minTXID && info.MaxTXID == maxTXID
	})
}

type gateKey struct{}

// gate pauses a background task at each storage call. The task sends the name
// of the call on at, then waits on resume.
type gate struct {
	at     chan string
	resume chan struct{}
}

func pause(ctx context.Context, format string, args ...any) {
	g, ok := ctx.Value(gateKey{}).(*gate)
	if !ok {
		return
	}
	g.at <- fmt.Sprintf(format, args...)
	<-g.resume
}

// task is a poll or compaction running on its own goroutine.
type task struct {
	name     string
	gate     gate
	done     chan error
	at       string
	finished bool
}

type harness struct {
	ctx    context.Context
	dir    string
	client *memClient
	f      *VFSFile
	pick   func(n int) int // returns a choice in [0, n)
	trace  []string

	pages   [][]byte // latest version of each page; pages[0] is page 1
	durable [][]byte // pages as of the last sync
	version uint64
	reading bool // holds SHARED across steps, like an open read transaction

	poll, compact *task
}

// failure is the panic value that stops a run at a failed check.
type failure struct{ msg string }

func newHarness(tb testing.TB, pick func(int) int) *harness {
	tb.Helper()
	h := &harness{ctx: tb.Context(), dir: tb.TempDir(), client: newMemClient(), pick: pick}
	f, err := openTestFile(h.dir, h.client, true)
	if err != nil {
		tb.Fatal(err)
	}
	tb.Cleanup(func() { _ = f.Close() })
	h.f = f
	return h
}

func openTestFile(dir string, client ReplicaClient, write bool) (*VFSFile, error) {
	f := NewVFSFile(client, "db", slog.New(slog.NewTextHandler(io.Discard, nil)))
	f.PollInterval = time.Hour // the test runs every poll
	f.CacheSize = 2 * ilPageSize
	if write {
		f.writeEnabled = true
		f.dirty = make(map[uint32]int64)
		f.syncInterval = 0
		f.bufferPath = filepath.Join(dir, "buffer")
	}
	if err := f.Open(); err != nil {
		return nil, err
	}
	return f, nil
}

func (h *harness) failf(format string, args ...any) {
	panic(failure{fmt.Sprintf(format, args...)})
}

func (h *harness) logf(format string, args ...any) {
	h.trace = append(h.trace, fmt.Sprintf(format, args...))
}

// do runs fn and returns the first failed check as an error that includes the
// steps leading up to it.
func (h *harness) do(fn func()) (err error) {
	defer func() {
		r := recover()
		if r == nil {
			return
		}
		f, ok := r.(failure)
		if !ok {
			panic(r)
		}
		h.abandon()
		trace := h.trace[max(0, len(h.trace)-60):]
		err = fmt.Errorf("%s\nlast %d steps:\n  %s", f.msg, len(trace), strings.Join(trace, "\n  "))
	}()
	fn()
	return nil
}

// abandon resumes paused tasks until they return, ignoring their errors.
func (h *harness) abandon() {
	for _, t := range []*task{h.poll, h.compact} {
		for t != nil && !t.finished {
			t.gate.resume <- struct{}{}
			select {
			case <-t.gate.at:
			case <-t.done:
				t.finished = true
			}
		}
	}
	h.poll, h.compact = nil, nil
}

func (h *harness) lock(l sqlite3vfs.LockType) {
	if err := h.f.Lock(l); err != nil {
		h.failf("lock %v: %v", l, err)
	}
}

func (h *harness) unlock(l sqlite3vfs.LockType) {
	if err := h.f.Unlock(l); err != nil {
		h.failf("unlock %v: %v", l, err)
	}
}

// pageData returns version v of page pgno. The first 12 bytes hold the page
// number and version so that a failed check can name the version it read.
func pageData(pgno uint32, v uint64) []byte {
	b := make([]byte, ilPageSize)
	binary.BigEndian.PutUint32(b[0:4], pgno)
	binary.BigEndian.PutUint64(b[4:12], v)
	for i := 32; i+8 <= len(b); i += 8 {
		binary.BigEndian.PutUint64(b[i:], v*0x9e3779b97f4a7c15^uint64(i))
	}
	return b
}

func describePage(b []byte) string {
	if bytes.Equal(b, make([]byte, len(b))) {
		return "zeros"
	}
	return fmt.Sprintf("page %d version %d", binary.BigEndian.Uint32(b[0:4]), binary.BigEndian.Uint64(b[4:12]))
}

// samePage compares page contents. ReadAt rewrites bytes 18-19 and 24-27 of
// page 1 to look like rollback-journal mode, so the comparison skips them.
func samePage(pgno uint32, got, want []byte) bool {
	if pgno != 1 {
		return bytes.Equal(got, want)
	}
	return bytes.Equal(got[:18], want[:18]) && bytes.Equal(got[20:24], want[20:24]) && bytes.Equal(got[28:], want[28:])
}

func (h *harness) checkPage(f *VFSFile, pages [][]byte, pgno uint32, why string) {
	got := make([]byte, ilPageSize)
	if _, err := f.ReadAt(got, int64(pgno-1)*ilPageSize); err != nil {
		h.failf("%s: read page %d: %v", why, pgno, err)
	}
	if want := pages[pgno-1]; !samePage(pgno, got, want) {
		h.failf("%s: page %d returned %s, want %s", why, pgno, describePage(got), describePage(want))
	}
}

func (h *harness) checkFile(f *VFSFile, pages [][]byte, why string) {
	size, err := f.FileSize()
	if err != nil {
		h.failf("%s: file size: %v", why, err)
	}
	if want := int64(len(pages)) * ilPageSize; size != want {
		h.failf("%s: FileSize returned %d pages, want %d", why, size/ilPageSize, len(pages))
	}
	for pgno := range len(pages) {
		h.checkPage(f, pages, uint32(pgno+1), why)
	}
}

// write commits one write transaction that writes pgnos in order. A page
// number past the end of the database must be the next page.
func (h *harness) write(pgnos ...uint32) {
	h.logf("write pages %v", pgnos)
	if !h.reading {
		h.lock(sqlite3vfs.LockShared)
	}
	h.lock(sqlite3vfs.LockReserved)
	h.lock(sqlite3vfs.LockExclusive)
	for _, pgno := range pgnos {
		switch {
		case int(pgno) <= len(h.pages):
			// SQLite reads a page before it changes it, so a stale read here
			// is how a wrong page reaches the replica.
			h.checkPage(h.f, h.pages, pgno, "read before write")
		case int(pgno) == len(h.pages)+1:
			h.pages = append(h.pages, nil)
		default:
			h.failf("write page %d: database has %d pages", pgno, len(h.pages))
		}
		h.version++
		b := pageData(pgno, h.version)
		if _, err := h.f.WriteAt(b, int64(pgno-1)*ilPageSize); err != nil {
			h.failf("write page %d: %v", pgno, err)
		}
		h.pages[pgno-1] = b
	}
	h.unlock(sqlite3vfs.LockShared)
	if !h.reading {
		h.unlock(sqlite3vfs.LockNone)
	}
}

func (h *harness) sync() {
	h.logf("sync")
	if err := h.f.Sync(sqlite3vfs.SyncNormal); err != nil {
		h.failf("sync: %v", err)
	}
	h.durable = slices.Clone(h.pages)
}

func (h *harness) checkAll(why string) {
	h.logf("check all pages (%s)", why)
	if !h.reading {
		h.lock(sqlite3vfs.LockShared)
		defer h.unlock(sqlite3vfs.LockNone)
	}
	h.checkFile(h.f, h.pages, why)
}

// checkReplica opens a second VFSFile on the same storage, as a cold start
// does, and compares it with the pages as of the last sync.
func (h *harness) checkReplica() {
	h.logf("check replica with a second VFSFile")
	if len(h.durable) == 0 {
		return
	}
	g, err := openTestFile(h.dir, h.client, false)
	if err != nil {
		h.failf("open replica: %v", err)
	}
	defer func() { _ = g.Close() }()
	if err := g.Lock(sqlite3vfs.LockShared); err != nil {
		h.failf("lock replica: %v", err)
	}
	h.checkFile(g, h.durable, "replica")
}

func (h *harness) toggleRead() {
	if h.reading {
		h.logf("end read")
		h.reading = false
		h.unlock(sqlite3vfs.LockNone)
		return
	}
	h.logf("begin read")
	h.lock(sqlite3vfs.LockShared)
	h.reading = true
}

func (h *harness) start(name string, run func(ctx context.Context) error) *task {
	h.logf("start %s", name)
	t := &task{name: name, gate: gate{at: make(chan string), resume: make(chan struct{})}, done: make(chan error, 1)}
	ctx := context.WithValue(h.ctx, gateKey{}, &t.gate)
	go func() { t.done <- run(ctx) }()
	if h.await(t) {
		return nil
	}
	return t
}

// await waits until t pauses at its next storage call or returns, and reports
// whether it returned.
func (h *harness) await(t *task) bool {
	select {
	case t.at = <-t.gate.at:
		h.logf("  %s paused at %s", t.name, t.at)
		return false
	case err := <-t.done:
		t.finished = true
		if err != nil && !errors.Is(err, ErrNoCompaction) {
			h.failf("%s: %v", t.name, err)
		}
		h.logf("  %s returned", t.name)
		return true
	}
}

func (h *harness) resume(t *task) bool {
	t.gate.resume <- struct{}{}
	return h.await(t)
}

func (h *harness) startPoll() { h.poll = h.start("poll", h.f.pollReplicaClient) }

func (h *harness) startCompaction() {
	c := NewCompactor(h.client, slog.New(slog.NewTextHandler(io.Discard, nil)))
	h.compact = h.start("L1 compaction", func(ctx context.Context) error {
		_, err := c.Compact(ctx, 1)
		return err
	})
}

func (h *harness) stepPoll() {
	if h.resume(h.poll) {
		h.poll = nil
	}
}

func (h *harness) stepCompaction() {
	if h.resume(h.compact) {
		h.compact = nil
	}
}

// stepPollTo resumes the poll until it pauses at the named storage call.
func (h *harness) stepPollTo(at string) {
	for h.poll != nil && h.poll.at != at {
		h.stepPoll()
	}
	if h.poll == nil {
		h.failf("poll returned before %s", at)
	}
}

func (h *harness) stepCompactionTo(at string) {
	for h.compact != nil && h.compact.at != at {
		h.stepCompaction()
	}
	if h.compact == nil {
		h.failf("compaction returned before %s", at)
	}
}

func (h *harness) finishTasks() {
	for h.poll != nil {
		h.stepPoll()
	}
	for h.compact != nil {
		h.stepCompaction()
	}
}

func (h *harness) pollNow() {
	if h.poll == nil {
		h.startPoll()
	}
	h.finishTasks()
}

func (h *harness) compactNow() {
	if h.compact == nil {
		h.startCompaction()
	}
	h.finishTasks()
}

func (h *harness) randomWrite() {
	var pgnos []uint32
	next := uint32(len(h.pages)) + 1
	for range 1 + h.pick(3) {
		if len(h.pages) == 0 || (next <= ilMaxPages && h.pick(4) == 0) {
			pgnos = append(pgnos, next)
			next++
		} else {
			pgnos = append(pgnos, uint32(1+h.pick(len(h.pages))))
		}
	}
	h.write(pgnos...)
}

func (h *harness) randomStep() {
	switch r := h.pick(100); {
	case r < 30:
		h.randomWrite()
	case r < 45:
		h.sync()
	case r < 65:
		if h.poll == nil {
			h.startPoll()
		} else {
			h.stepPoll()
		}
	case r < 77:
		if h.compact == nil {
			h.startCompaction()
		} else {
			h.stepCompaction()
		}
	case r < 90:
		h.checkAll("read")
	case r < 97:
		h.toggleRead()
	default:
		h.checkReplica()
	}
}

// runRandom takes up to steps random steps, then lets background tasks
// finish, syncs, polls, and checks the file and the replica.
func (h *harness) runRandom(steps int, exhausted func() bool) error {
	return h.do(func() {
		for i := 0; i < steps && !exhausted(); i++ {
			h.randomStep()
		}
		h.finishTasks()
		if h.reading {
			h.toggleRead()
		}
		h.sync()
		h.pollNow()
		h.checkAll("after final sync and poll")
		h.checkReplica()
	})
}

// A poll that lists L0 before a sync must not move the position back to
// before that sync. If it does, the next poll reads the synced file again,
// compares its smaller commit with a page count that includes unsynced pages,
// takes that as a shrink, and drops every page the file doesn't contain.
func TestInterleavePollDoesNotRewindPosition(t *testing.T) {
	h := newHarness(t, nil)
	if err := h.do(func() {
		h.write(1, 2, 3)
		h.sync()
		h.startPoll()
		h.stepPollTo("listed L0")
		h.write(2)
		h.sync()
		h.write(4)
		h.finishTasks()
		h.pollNow()
		h.checkAll("after polls")
	}); err != nil {
		t.Fatal(err)
	}
}

// An L1 file that ends before the newest L0 file has a smaller commit only
// because it's older. Taking that as a shrink replaces the page index with
// the L1 file's pages and drops the pages written after it.
func TestInterleaveOlderL1IsNotAShrink(t *testing.T) {
	h := newHarness(t, nil)
	if err := h.do(func() {
		h.write(1, 2, 3)
		h.sync()
		h.compactNow()
		h.write(4)
		h.sync()
		h.pollNow()
		h.checkAll("after poll")
	}); err != nil {
		t.Fatal(err)
	}
}

// When one poll finds two new L1 files, the first can end before the L0
// position and have a smaller commit only because it's older. That must not
// replace the index because the last L1 file reaches the L0 position.
func TestInterleaveTwoNewL1FilesAreNotAShrink(t *testing.T) {
	h := newHarness(t, nil)
	if err := h.do(func() {
		h.write(1, 2, 3)
		h.sync()
		h.compactNow()
		h.pollNow()
		h.write(4)
		h.sync()
		h.compactNow()
		h.write(5)
		h.sync()
		h.compactNow()
		h.pollNow()
		h.checkAll("after poll")
	}); err != nil {
		t.Fatal(err)
	}
}

// A compaction that lists L0 before a sync writes an L1 file older than that
// sync. When a poll finds it after installing the newer L0 page, the older
// L1 entry must not replace it.
func TestInterleaveOlderL1EntryDoesNotReplaceNewerL0(t *testing.T) {
	h := newHarness(t, nil)
	if err := h.do(func() {
		h.write(1, 2)
		h.sync()
		h.startCompaction()
		h.stepCompactionTo("listed L0")
		h.write(1)
		h.sync()
		h.pollNow()
		h.finishTasks()
		h.pollNow()
		h.checkAll("after polls")
	}); err != nil {
		t.Fatal(err)
	}
}

// TestInterleaveRandom runs random schedules of writes, syncs, reads, and
// paused polls and compactions. To run more schedules, set
// LITEVFS_INTERLEAVE_SEEDS. To replay one, set LITEVFS_INTERLEAVE_SEED.
func TestInterleaveRandom(t *testing.T) {
	first, n := int64(1), int64(200)
	if testing.Short() {
		n = 50
	}
	if s := os.Getenv("LITEVFS_INTERLEAVE_SEEDS"); s != "" {
		v, err := strconv.ParseInt(s, 10, 64)
		if err != nil {
			t.Fatal(err)
		}
		n = v
	}
	if s := os.Getenv("LITEVFS_INTERLEAVE_SEED"); s != "" {
		v, err := strconv.ParseInt(s, 10, 64)
		if err != nil {
			t.Fatal(err)
		}
		first, n = v, 1
	}
	for seed := first; seed < first+n; seed++ {
		rng := rand.New(rand.NewSource(seed))
		h := newHarness(t, rng.Intn)
		if err := h.runRandom(150, func() bool { return false }); err != nil {
			t.Fatalf("seed %d: %v\nTo replay, set LITEVFS_INTERLEAVE_SEED=%d.", seed, err, seed)
		}
	}
}

// FuzzInterleave reads each choice of the random schedule from the input, so
// coverage-guided fuzzing can search for schedules that fail.
func FuzzInterleave(f *testing.F) {
	f.Add([]byte{0, 0, 30, 40, 50, 60, 60, 60, 0, 30, 45, 60, 60, 80, 85})
	f.Add([]byte{0, 1, 2, 30, 70, 70, 70, 0, 3, 30, 50, 50, 50, 50, 70, 70, 50, 50, 85})
	f.Fuzz(func(t *testing.T, choices []byte) {
		i := 0
		pick := func(n int) int {
			if i >= len(choices) {
				return 0
			}
			i++
			return int(choices[i-1]) % n
		}
		h := newHarness(t, pick)
		if err := h.runRandom(len(choices), func() bool { return i >= len(choices) }); err != nil {
			t.Fatal(err)
		}
	})
}
