package agent

import (
	"context"
	"encoding/json"
	"errors"
	"net"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/imjasonh/playground/sshcloud/internal/helperrpc"
	"github.com/imjasonh/playground/sshcloud/internal/vmmhelper"
)

func TestHelperRuntimePropagatesLaunchFailure(t *testing.T) {
	t.Parallel()
	dir := t.TempDir()
	vmmSocket := filepath.Join(dir, "vmm.sock")
	tapSocket := filepath.Join(dir, "tap.sock")
	vmmListener := serveTestHelper(t, vmmSocket, func(_ context.Context, operation string, _ json.RawMessage) (any, error) {
		if operation == "launch" {
			return nil, errors.New("injected jailer failure")
		}
		return nil, nil
	})
	defer vmmListener.Close()
	tapListener := serveTestHelper(t, tapSocket, func(context.Context, string, json.RawMessage) (any, error) {
		return nil, nil
	})
	defer tapListener.Close()

	runtime := NewHelperRuntime(vmmSocket, tapSocket)
	if err := runtime.Ready(context.Background()); err != nil {
		t.Fatal(err)
	}
	_, _, err := runtime.Boot(context.Background(), BootSpec{
		WorkDir:     filepath.Join(dir, "vm-0123abcdef89"),
		TapName:     "fc-0123abcdef89",
		GuestIP:     "172.16.2.2",
		GuestMAC:    "AA:FC:00:00:00:01",
		BootArgs:    "init=/platform-init",
		VCPUs:       1,
		MemMiB:      128,
		CPUTemplate: "T2",
	})
	if err == nil || !strings.Contains(err.Error(), "injected jailer failure") {
		t.Fatalf("Boot error = %v", err)
	}
	var remote *helperrpc.RemoteError
	if !errors.As(err, &remote) {
		t.Fatalf("Boot error type = %T, want RemoteError", err)
	}
}

func TestHelperMachineLivenessFailsClosed(t *testing.T) {
	t.Parallel()
	machine := &helperMachine{
		vmID: "0123abcdef89",
		vmm:  vmmhelper.Client{SocketPath: filepath.Join(t.TempDir(), "missing.sock")},
	}
	if machine.Alive() {
		t.Fatal("unreachable lifecycle helper reported VM alive")
	}
}

func serveTestHelper(t *testing.T, socket string, handler helperrpc.Handler) net.Listener {
	t.Helper()
	listener, err := net.Listen("unix", socket)
	if err != nil {
		t.Fatal(err)
	}
	go func() {
		_ = helperrpc.Serve(listener, uint32(os.Getuid()), handler)
	}()
	return listener
}
