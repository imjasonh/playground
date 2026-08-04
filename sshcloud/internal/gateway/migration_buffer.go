package gateway

import (
	"io"
	"sync"
)

const defaultMigrationBufferBytes = 1 << 20

// migrationInput is the sole reader of the outer SSH channel. Backend
// attachments consume from one bounded queue; detaching an old backend leaves
// subsequent client bytes queued for the replacement backend.
type migrationInput struct {
	source io.Reader
	max    int

	mu       sync.Mutex
	cond     *sync.Cond
	data     []byte
	activeID uint64
	closed   bool
	overflow chan struct{}
	once     sync.Once
}

func newMigrationInput(source io.Reader, max int) *migrationInput {
	if max <= 0 {
		max = defaultMigrationBufferBytes
	}
	b := &migrationInput{source: source, max: max, overflow: make(chan struct{})}
	b.cond = sync.NewCond(&b.mu)
	go b.readSource()
	return b
}

func (b *migrationInput) readSource() {
	buf := make([]byte, 32<<10)
	for {
		n, err := b.source.Read(buf)
		b.mu.Lock()
		if n > 0 {
			if len(b.data)+n > b.max {
				b.once.Do(func() { close(b.overflow) })
			} else {
				b.data = append(b.data, buf[:n]...)
				b.cond.Broadcast()
			}
		}
		if err != nil {
			b.closed = true
			b.cond.Broadcast()
			b.mu.Unlock()
			return
		}
		b.mu.Unlock()
	}
}

func (b *migrationInput) Attach() *migrationAttachment {
	b.mu.Lock()
	defer b.mu.Unlock()
	b.activeID++
	id := b.activeID
	b.cond.Broadcast()
	return &migrationAttachment{buffer: b, id: id}
}

func (b *migrationInput) Overflow() <-chan struct{} { return b.overflow }

func (b *migrationInput) Close() {
	b.mu.Lock()
	b.closed = true
	b.activeID++
	b.cond.Broadcast()
	b.mu.Unlock()
}

type migrationAttachment struct {
	buffer *migrationInput
	id     uint64
	once   sync.Once
}

func (a *migrationAttachment) Read(p []byte) (int, error) {
	b := a.buffer
	b.mu.Lock()
	defer b.mu.Unlock()
	for {
		if a.id != b.activeID {
			return 0, io.EOF
		}
		if len(b.data) > 0 {
			n := copy(p, b.data)
			b.data = b.data[n:]
			return n, nil
		}
		if b.closed {
			return 0, io.EOF
		}
		b.cond.Wait()
	}
}

func (a *migrationAttachment) Close() error {
	a.once.Do(func() {
		b := a.buffer
		b.mu.Lock()
		if b.activeID == a.id {
			b.activeID++
			b.cond.Broadcast()
		}
		b.mu.Unlock()
	})
	return nil
}
