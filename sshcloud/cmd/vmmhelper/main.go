// Command vmmhelper is the root-owned Firecracker jailer/process boundary.
package main

import (
	"context"
	"flag"
	"log"
	"math"
	"net"
	"os"
	"os/signal"
	"syscall"

	"github.com/imjasonh/playground/sshcloud/internal/helperrpc"
	"github.com/imjasonh/playground/sshcloud/internal/hostisolation"
	"github.com/imjasonh/playground/sshcloud/internal/vmmhelper"
)

func main() {
	socketActivation := flag.Bool("socket-activation", false, "accept the single systemd-provided socket")
	socketPath := flag.String("socket", "/run/sshcloud/vmmhelper.sock", "local helper socket (without socket activation)")
	workRoot := flag.String("work-root", "/var/lib/sshcloud/agent", "fixed agent VM work root")
	chrootBase := flag.String("chroot-base", "/var/lib/sshcloud/jailer", "fixed jailer chroot base")
	firecracker := flag.String("firecracker", "/var/lib/sshcloud/assets/firecracker", "pinned Firecracker v1.10.1")
	jailer := flag.String("jailer", "/var/lib/sshcloud/assets/jailer", "pinned jailer v1.10.1")
	kernel := flag.String("kernel", "/var/lib/sshcloud/assets/vmlinux", "fixed platform kernel")
	proxyDir := flag.String("proxy-dir", "/run/sshcloud/vmm-api", "fixed per-VM API proxy directory")
	cgroupParent := flag.String("cgroup-parent", "sshcloud", "fixed cgroup v2 parent")
	agentUID := flag.Uint("agent-uid", 0, "authorized unprivileged agent UID")
	agentGID := flag.Uint("agent-gid", 0, "agent GID owning exported files and API sockets")
	sandboxIDBase := flag.Uint("sandbox-id-base", uint(hostisolation.DefaultSandboxIDBase), "first sandbox UID/GID")
	flag.Parse()

	for label, value := range map[string]uint{
		"agent UID":       *agentUID,
		"agent GID":       *agentGID,
		"sandbox ID base": *sandboxIDBase,
	} {
		if value == 0 || value > math.MaxUint32 {
			log.Fatalf("%s must be a nonzero uint32", label)
		}
	}
	server, err := vmmhelper.NewServer(vmmhelper.Config{
		WorkRoot:       *workRoot,
		ChrootBase:     *chrootBase,
		Firecracker:    *firecracker,
		Jailer:         *jailer,
		Kernel:         *kernel,
		ProxyDir:       *proxyDir,
		CgroupParent:   *cgroupParent,
		AgentUID:       uint32(*agentUID),
		AgentGID:       uint32(*agentGID),
		SandboxIDBase:  uint32(*sandboxIDBase),
		ExpectedPeerID: uint32(*agentUID),
	})
	if err != nil {
		log.Fatal(err)
	}
	if err := server.Ready(context.Background()); err != nil {
		log.Fatalf("VMM helper readiness: %v", err)
	}
	if err := server.CleanupOrphans(); err != nil {
		log.Fatalf("VMM helper orphan cleanup: %v", err)
	}

	var listener net.Listener
	if *socketActivation {
		listener, err = helperrpc.ActivatedListener()
	} else {
		listener, err = helperrpc.ListenPath(*socketPath, int(*agentUID), int(*agentGID))
	}
	if err != nil {
		log.Fatal(err)
	}
	defer listener.Close()

	serveErr := make(chan error, 1)
	go func() { serveErr <- server.Serve(listener) }()
	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()
	select {
	case <-ctx.Done():
		_ = listener.Close()
	case err := <-serveErr:
		if err != nil {
			log.Printf("VMM helper listener: %v", err)
		}
	}
	if err := server.Close(); err != nil {
		log.Printf("VMM helper cleanup: %v", err)
	}
}
