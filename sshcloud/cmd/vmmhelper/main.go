// Command vmmhelper is the root-owned Firecracker jailer/process boundary.
package main

import (
	"context"
	"flag"
	"log"
	"math"
	"net"
	"net/http"
	"os"
	"os/signal"
	"syscall"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/helperrpc"
	"github.com/imjasonh/playground/sshcloud/internal/observability"
	"github.com/imjasonh/playground/sshcloud/internal/vmmhelper"
)

func main() {
	observability.Configure("vmmhelper")
	socketActivation := flag.Bool("socket-activation", false, "accept the single systemd-provided socket")
	socketPath := flag.String("socket", "/run/sshcloud/vmmhelper.sock", "local helper socket (without socket activation)")
	metricsListen := flag.String("metrics-listen", "127.0.0.1:9080", "loopback-only aggregate metrics listen address")
	hostID := flag.String("host-id", "", "fixed host attribution (default: local hostname)")
	workRoot := flag.String("work-root", "/var/lib/sshcloud/agent", "fixed agent VM work root")
	chrootBase := flag.String("chroot-base", "/var/lib/sshcloud/jailer", "fixed jailer chroot base")
	firecracker := flag.String("firecracker", "/var/lib/sshcloud/assets/firecracker", "pinned Firecracker v1.10.1")
	jailer := flag.String("jailer", "/var/lib/sshcloud/assets/jailer", "pinned jailer v1.10.1")
	kernel := flag.String("kernel", "/var/lib/sshcloud/assets/vmlinux", "fixed platform kernel")
	proxyDir := flag.String("proxy-dir", "/run/sshcloud/vmm-api", "fixed per-VM API proxy directory")
	cgroupParent := flag.String("cgroup-parent", "sshcloud", "fixed cgroup v2 parent")
	agentUID := flag.Uint("agent-uid", 0, "authorized unprivileged agent UID")
	agentGID := flag.Uint("agent-gid", 0, "agent GID owning exported files and API sockets")
	flag.Parse()

	for label, value := range map[string]uint{
		"agent UID": *agentUID,
		"agent GID": *agentGID,
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
		ExpectedPeerID: uint32(*agentUID),
		HostID:         *hostID,
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

	var metricsServer *http.Server
	if *metricsListen != "" {
		host, _, err := net.SplitHostPort(*metricsListen)
		if err != nil || net.ParseIP(host) == nil || !net.ParseIP(host).IsLoopback() {
			log.Fatal("-metrics-listen must use a literal loopback address")
		}
		metricsServer = &http.Server{
			Addr: *metricsListen, Handler: observability.MetricsHandler(),
			ReadHeaderTimeout: 5 * time.Second, ReadTimeout: 5 * time.Second,
			WriteTimeout: 5 * time.Second, IdleTimeout: 30 * time.Second,
		}
		go func() {
			if err := metricsServer.ListenAndServe(); err != nil && err != http.ErrServerClosed {
				log.Printf("VMM helper metrics: %v", err)
			}
		}()
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
	if metricsServer != nil {
		shutdown, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		_ = metricsServer.Shutdown(shutdown)
		cancel()
	}
}
