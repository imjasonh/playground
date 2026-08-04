package agent

import (
	"context"
	"fmt"
	"net"
	"os"
	"path/filepath"
	"sync"
	"sync/atomic"

	"github.com/imjasonh/playground/sshcloud/internal/firecracker"
	"github.com/imjasonh/playground/sshcloud/internal/rootfs"
)

// FakeRuntime boots localhost TCP listeners instead of Firecracker.
// Used for migrate/sleep tests without /dev/kvm. Snapshot files carry a
// generation token so restore proves the package was loaded.
type FakeRuntime struct {
	seq atomic.Uint64
}

func (FakeRuntime) Available() bool { return true }

func (r *FakeRuntime) Boot(ctx context.Context, spec BootSpec) (machine, string, error) {
	_ = ctx
	if err := ensureRootfsFile(spec.RootfsPath); err != nil {
		return nil, "", err
	}
	return r.listen(fmt.Sprintf("boot-%d", r.seq.Add(1)))
}

func (r *FakeRuntime) Restore(ctx context.Context, spec RestoreSpec) (machine, string, error) {
	_ = ctx
	if err := rootfs.Clone(spec.RootfsSrc, spec.RootfsDst); err != nil {
		return nil, "", err
	}
	token, err := os.ReadFile(spec.StatePath)
	if err != nil {
		return nil, "", fmt.Errorf("read vm.state: %w", err)
	}
	if len(token) == 0 {
		return nil, "", fmt.Errorf("empty vm.state")
	}
	mem, err := os.ReadFile(spec.MemPath)
	if err != nil {
		return nil, "", fmt.Errorf("read vm.mem: %w", err)
	}
	if string(mem) != "mem:"+string(token) {
		return nil, "", fmt.Errorf("vm.mem does not match vm.state")
	}
	return r.listen("restore:" + string(token))
}

func (r *FakeRuntime) listen(token string) (machine, string, error) {
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		return nil, "", err
	}
	fm := &fakeMachine{ln: ln, token: token, addr: ln.Addr().String()}
	go fm.acceptLoop()
	return fm, fm.addr, nil
}

type fakeMachine struct {
	mu     sync.Mutex
	ln     net.Listener
	token  string
	addr   string
	closed bool
}

func (m *fakeMachine) acceptLoop() {
	for {
		c, err := m.ln.Accept()
		if err != nil {
			return
		}
		_ = c.Close()
	}
}

func (m *fakeMachine) SnapshotThenKill(_ context.Context, files firecracker.SnapshotFiles) error {
	m.mu.Lock()
	defer m.mu.Unlock()
	if m.closed {
		return fmt.Errorf("already stopped")
	}
	if err := os.MkdirAll(filepath.Dir(files.StatePath), 0o755); err != nil {
		return err
	}
	if err := os.WriteFile(files.StatePath, []byte(m.token), 0o644); err != nil {
		return err
	}
	if err := os.WriteFile(files.MemPath, []byte("mem:"+m.token), 0o644); err != nil {
		return err
	}
	_ = m.ln.Close()
	m.closed = true
	return nil
}

func (m *fakeMachine) Stop() error { return m.Kill() }

func (m *fakeMachine) Kill() error {
	m.mu.Lock()
	defer m.mu.Unlock()
	if m.closed {
		return nil
	}
	err := m.ln.Close()
	m.closed = true
	return err
}
