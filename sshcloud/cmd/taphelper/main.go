// Command taphelper is the CAP_NET_ADMIN-only TAP/network boundary.
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
	"github.com/imjasonh/playground/sshcloud/internal/observability"
	"github.com/imjasonh/playground/sshcloud/internal/taphelper"
)

func main() {
	observability.Configure("taphelper")
	socketActivation := flag.Bool("socket-activation", false, "accept the single systemd-provided socket")
	socketPath := flag.String("socket", "/run/sshcloud/taphelper.sock", "local helper socket (without socket activation)")
	agentUID := flag.Uint("agent-uid", 0, "authorized unprivileged agent UID")
	agentGID := flag.Uint("agent-gid", 0, "agent GID owning a direct-mode socket")
	subnetBase := flag.String("subnet-base", "172.16", "fixed first two IPv4 octets")
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
	server, err := taphelper.NewServer(taphelper.Config{
		SubnetBase:      *subnetBase,
		SandboxIDBase:   uint32(*sandboxIDBase),
		ExpectedPeerUID: uint32(*agentUID),
	})
	if err != nil {
		log.Fatal(err)
	}
	if err := server.Ready(context.Background()); err != nil {
		log.Fatalf("TAP helper readiness: %v", err)
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
			log.Printf("TAP helper listener: %v", err)
		}
	}
}
